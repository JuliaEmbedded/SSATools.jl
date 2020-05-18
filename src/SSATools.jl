module SSATools

#SSA manipulation package
    #insert
    #delete
    #replace
    #function walking
    #turn that back in to an anon function that can be evaluated

export ci_to_f, cfg_to_lightgraph, CDFG, get_cdfg

using LightGraphs, MetaGraphs, LinearAlgebra, MacroTools #,Gadfly, GraphPlot
using Core.Compiler: CodeInfo, SlotNumber

function globref_to_func(g::GlobalRef)
    func_str = repr(g)
    func_str = func_str[3:(length(func_str)-1)]
    func = eval(Meta.parse(func_str)) #convert to a function call
    return func
end

const ignore_f = [Symbol("gotoifnot"), Symbol("return"), Symbol("unreachable")]
function fcgraph_rec!(fcg::MetaDiGraph, depth::Int64, parentindex::Int64, func::Any, input_types) #include function list?
    func_list = []

    q_tt = quote Tuple{$(input_types...)} end
    tt = eval(q_tt)
    ci = code_typed(func, tt)[1][1]

    if !ci.inferred
        error("CodeInfo object has no type inference")
    else
        for (line, type) in zip(ci.code, ci.ssavaluetypes)
            if isa(line, Expr) #ignore non functions, phi nodes
                if line.head ∉ ignore_f
                    if line.head == :invoke #if the node is an invoke node, the first arg is the method instance
                        func_called = line.args[2] #quote $(line.args[3]...) end
                    else
                        func_called = line.args[1] #quote $(line.args[3]...) end
                    end

                    #=if line.head == :new
                        type_repr = repr(line.args[1])
                        if occursin("getfield(Main, Symbol(\"#") && !occursin("Base.Generator")
                            #indicates an anonymous function created by the compiler
                            #eval the line Expr, replace args[2:end] with instances of their type
                            #type information provided between { } in arg 1
                            #not sure if there's a better way to get them out without using repr
                            #use zero(Type)  for int, float, etc
                            #use zeros(Type, dim_n, dim_m...) for arrays
                            #might need to add lookup for strings and char and other missing types
                        end
                    end=#

                    if func_called ∉ func_list #only add new functions to the fcg
                        push!(func_list, func_called)
                        LightGraphs.add_vertex!(fcg) #add vertex
                        MetaGraphs.set_props!(fcg, LightGraphs.nv(fcg), #set meta data of just-added node
                                                            Dict( :Level=>depth+1,
                                                            :Head=>line.head,
                                                            #:Expr=>line,#rpl_slotnums(line, ci.slotnames),
                                                            :Func=>func_called,
                                                            :Type=>type))
                        LightGraphs.add_edge!(fcg, parentindex, LightGraphs.nv(fcg)) #connect node to graph

                        if line.head == :foreigncall
                            #calls to underlying c functions, e.g., array allocation
                            #println("No split ",LightGraphs.nv(fcg))
                        else
                            #println(func_called, typeof(func_called))
                            if typeof(func_called) in [Type, DataType]
                                #println("No split - type inst ",LightGraphs.nv(fcg))
                            elseif (func_called.mod == Base || func_called.mod == Core)
                                #println("No split - module ",LightGraphs.nv(fcg))
                            elseif func_called.name == :throw
                                #println("No split - function",LightGraphs.nv(fcg))
                            else
                                #nodes that aren't at base should be split, turn the ref into a function call
                                l_f = globref_to_func(func_called)
                                #get the types required for the function call
                                #arg 1 is method instance, 2 is globalref to function, 3 onward are vars for the function
                                arg_list = []
                                for arg_i in 3:length(line.args)
                                    if isa(line.args[arg_i], Core.SSAValue)
                                        #replace with the type in the slot num
                                        ssaid = line.args[arg_i].id
                                        push!(arg_list, ci.ssavaluetypes[ssaid])
                                    elseif isa(line.args[arg_i], Core.SlotNumber)
                                        #replace with a type from the input_types
                                        sltid = line.args[arg_i].id - 1
                                        push!(arg_list, input_types[sltid])
                                    else
                                        #Otherwise just use the type.
                                        push!(arg_list, typeof(line.args[arg_i]))
                                    end
                                end

                                fcgraph_rec!(fcg, depth+1, LightGraphs.nv(fcg), l_f, arg_list)
                            end
                        end
                    end
                end
            end
        end
    end
end

function fcgraph(func::Any, input_types::Type...)
    #assuming input types can be provided
    fcg = MetaDiGraph(SimpleDiGraph(1))
    MetaGraphs.set_props!(fcg, 1, Dict(:Level=>"1-Main", :Expr=>:(), :Type=>:()))
    func_list = []
    depth = 1

    fcgraph_rec!(fcg, depth, 1, func, input_types)

    return fcg
end

function printfcg_vdict(fcg)
    #ignore main
    for i in 2:LightGraphs.nv(fcg) #vertices
        println(MetaGraphs.props(fcg, i))
    end
end

#inserts an expression into the code
#inserted expressions using a given function need
#to be a GlobalRef type rather than :() expressions or symbols
function ci_insert!(cicp::CodeInfo, pos::Int, ins)
    if isa(cicp.code[pos], Core.GotoNode)
        #targeting a solo goto branch, why does the copiler even make these???
        targeting_goto = true
    else
        targeting_goto = false
    end

    insert!(cicp.code, pos, ins)
    insert!(cicp.ssavaluetypes, pos, Any)
    insert!(cicp.codelocs, pos, Int32(0))
    insert!(cicp.ssaflags, pos, UInt8(0))

    for (i, line) in enumerate(cicp.code)
        if isa(line, Expr)
            if line.head == :gotoifnot
                if isa(line.args[1], Core.SSAValue) # this is the var for the conditional
                    line.args[1] = (line.args[1].id >= pos) ? Core.SSAValue(line.args[1].id + 1) : line.args[1]
                end
                #this is the target line to branch to
                if line.args[2] > pos
                    line.args[2] += 1
                elseif line.args[2] == pos && !targeting_goto
                    line.args[2] += 1
                end
            else
                for (j,arg) in enumerate(line.args)
                    if isa(arg, Core.SSAValue)
                        if arg.id >= pos
                            line.args[j] = Core.SSAValue(arg.id + 1)
                        end
                    end
                end
            end
        elseif isa(line, Core.GotoNode)
            if line.label > pos
                cicp.code[i] = Core.GotoNode(line.label + 1)
            elseif line.label == pos && !targeting_goto
                cicp.code[i] = Core.GotoNode(line.label + 1)
            end
        elseif isa(line, Core.PhiNode)
            #println("edges: ", line.edges, " values: ", line.values)
            rpl_edges = Any[  (ssa >= pos) ?
                            (ssa + 1) : ssa
                            for ssa in line.edges]
            rpl_values = Any[ (isa(val, Core.SSAValue)) ?
                            ((val.id >= pos) ? Core.SSAValue(val.id + 1) : val) : val
                            for val in line.values]
            cicp.code[i] = Core.PhiNode(rpl_edges, rpl_values)
        elseif isa(line, Nothing)
        else
            println("type: ", typeof(line), " line: ", line)
            error()
        end
    end
end

function ci_delete!(cicp::CodeInfo, pos::Int; preserve_branch=false)
    deleteat!(cicp.code, pos)
    deleteat!(cicp.ssavaluetypes, pos)
    deleteat!(cicp.codelocs, pos)
    deleteat!(cicp.ssaflags, pos)

    #naively update the ssa values, do not update branch targets if the 1st statement in a branch is delyeeted
    for (i, line) in enumerate(cicp.code)
        if isa(line, Expr)
            if line.head == :gotoifnot
                #if we need to preserve the branch links this gets more complicated :(
                if isa(line.args[1], Core.SSAValue)
                    line.args[1] = (line.args[1].id > pos) ? Core.SSAValue(line.args[1].id - 1) : line.args[1]
                end
                line.args[2] = (line.args[2] > pos) ? (line.args[2] - 1) : line.args[2]
            else
                for (j,arg) in enumerate(line.args)
                    if isa(arg, Core.SSAValue)
                        if arg.id >= pos
                            line.args[j] = Core.SSAValue(arg.id - 1)
                        end
                    end
                end
            end
        elseif isa(line, Core.GotoNode)
            if line.label > pos
                cicp.code[i] = Core.GotoNode(line.label - 1)
            end
        elseif isa(line, Core.PhiNode)
            #println("edges: ", line.edges, " values: ", line.values)
            rpl_edges = Any[  (ssa >= pos) ?
                            (ssa - 1) : ssa
                            for ssa in line.edges]
            rpl_values = Any[ (isa(val, Core.SSAValue)) ?
                            ((val.id >= pos) ? Core.SSAValue(val.id - 1) : val) : val
                            for val in line.values]
            cicp.code[i] = Core.PhiNode(rpl_edges, rpl_values)
        elseif isa(line, Nothing)
        else
            println("type: ", typeof(line), " line: ", line)
            error()
        end
    end
end

function ci_ssa_replace!(cicp::CodeInfo, ssa_tgt::Int, ssa_rpl::Int)
    for (i, line) in enumerate(cicp.code)
        if isa(line, Expr)
            if line.head == :gotoifnot
                if isa(line.args[1], Core.SSAValue)
                    line.args[1] = (line.args[1].id == ssa_tgt) ? Core.SSAValue(ssa_rpl) : line.args[1]
                end
                #line.args[2] = (line.args[2] > ssa_tgt) ? (line.args[2] - 1) : line.args[2]
            else
                for (j,arg) in enumerate(line.args)
                    if isa(arg, Core.SSAValue)
                        if arg.id == ssa_tgt
                            line.args[j] = Core.SSAValue(ssa_rpl)
                        end
                    end
                end
            end
        elseif isa(line, Core.GotoNode)
            #if line.label == ssa_tgt
            #    cicp.code[i] = Core.GotoNode(line.label - 1)
            #end
        elseif isa(line, Core.PhiNode)
            #println("edges: ", line.edges, " values: ", line.values)
            #rpl_edges = Any[  (ssa >= ssa_tgt) ?
            #                (ssa - 1) : ssa
            #                for ssa in line.edges]
            rpl_values = Any[ (isa(val, Core.SSAValue)) ?
                            ((val.id == ssa_tgt) ? Core.SSAValue(ssa_rpl) : val) : val
                            for val in line.values]
            cicp.code[i] = Core.PhiNode(line.edges, rpl_values)
        elseif isa(line, Nothing)
        else
            println("type: ", typeof(line), " line: ", line)
            error()
        end
    end
end

dummy() = return

function slots!(ci::CodeInfo)
  ss = Dict{Slot,SlotNumber}()
  for i = 1:length(ci.code)
    ci.code[i] = MacroTools.prewalk(ci.code[i]) do x
      x isa Slot || return x
      haskey(ss, x) && return ss[x]
      push!(ci.slotnames, x.id)
      push!(ci.slotflags, 0x00)
      ss[x] = SlotNumber(length(ci.slotnames))
    end
  end
  return ci
end

struct Slot
 id::Symbol
end
Base.show(io::IO, s::Slot) = print(io, "@", s.id)
phislot(b, i) = Slot(Symbol(:phi_, b, :_, i))

function rpl_phinodes(ci_og::CodeInfo)
    ci = copy(ci_og)
    ci_ir = Core.Compiler.inflate_ir(ci_og)

    #insert the replacement vars
    offset = 0
    ssaoffset_l = []
    og_cfg = copy(ci_ir.cfg.blocks)

    for bb in og_cfg
        for succ in bb.succs
            for (st_num,stmt) in enumerate(ci_ir.cfg.blocks[succ].stmts)
                if isa(ci_og.code[stmt], Core.PhiNode)
                    for (edge, val) in zip(ci_og.code[stmt].edges, ci_og.code[stmt].values)
                        if edge in bb.stmts
                            if isa(val, Core.SSAValue)
                                ssaoffset=0
                                for tg in ssaoffset_l
                                    if tg <= val.id
                                        ssaoffset+=1
                                    end
                                end
                                new_val = Core.SSAValue(val.id + ssaoffset)
                            else
                                new_val = val
                            end
                            push!(ssaoffset_l, bb.stmts[end])
                            ci_insert!(ci, bb.stmts[end]+offset, Expr(:(=), phislot(succ, st_num), new_val))
                            offset+=1
                        end
                    end
                end
            end
        end
    end

    ci_ir = Core.Compiler.inflate_ir(ci) #update the ir

    rpl_ssa = Dict() #create a dict that links SSA ids to their replacement phinode slots
    phi_list = [] #get the positions of all the phi nodes in the ssa
    for (b_num,bb) in enumerate(ci_ir.cfg.blocks)
        for (st_num,stmt) in enumerate(bb.stmts)
            if isa(ci.code[stmt], Core.PhiNode)
                rpl_ssa[stmt] = phislot(b_num, st_num)
                pushfirst!(phi_list, stmt)
            elseif isa(ci.code[stmt], Expr)
                if ci.code[stmt].head == :gotoifnot
                    #goto nodes should not contain this so should be ignored
                else
                    for (j,arg) in enumerate(ci.code[stmt].args)
                        if isa(arg, Core.SSAValue)
                            if haskey(rpl_ssa, arg.id)
                                ci.code[stmt].args[j] = rpl_ssa[arg.id]
                            end
                        end
                    end
                end
            elseif isa(ci.code[stmt], Core.GotoNode)
                #goto nodes should not contain this so should be ignored
            elseif isa(ci.code[stmt], Nothing)
            else
                println("type: ", typeof(line), " line: ", line)
                error()
            end
        end
    end

    #delete the phinodes
    for line_i in phi_list
        ci_delete!(ci, line_i)
    end
    slots!(ci)
    return ci
end

#code typed ci
function ci_to_f(ci_pair::Pair, nargs::Int64)
    #replace invoke nodes with standard calls, not sure if this is always safe
    ci_eval = copy(ci_pair[1])
    for (i, ref_line) in enumerate(ci_pair[1].code)
        if isa(ref_line, Expr)
            if ref_line.head == :invoke
                rep_expr = Expr(:call, ref_line.args[2:end]...)
                ci_eval.code[i] = rep_expr
            end
        end
    end

    pnl = [isa(line, Core.PhiNode) for line in ci_pair[1].code]
    ci_eval = (true in pnl) ? rpl_phinodes(ci_eval) : ci_eval

    if isa(ci_eval.ssavaluetypes, Array)
        ci_eval.ssavaluetypes = length(ci_eval.ssavaluetypes)
    end
    ci_eval.inferred = false
    ci_eval.slottypes = Nothing
    #ci_eval.ssaflags = Vector{UInt8}[]
    ci_eval.slotflags = UInt8[UInt8(0) for _ in 1:length(ci_eval.slotnames)]

    @eval @generated function $(gensym())($([Symbol(:arg, i) for i = 1:nargs]...))
        return  $ci_eval
    end
end

#code lowered ci
function ci_to_f(ci::CodeInfo, nargs::Int64)
    ci_eval = copy(ci)
    @eval @generated function $(gensym())($([Symbol(:arg, i) for i = 1:nargs]...))
        return $ci_eval
    end
end

#CodeInfo Passes
function remove_sext_64!(ci::CodeInfo)

    del_list = [[], []]
    for (line_num, line) in enumerate(ci.code)
        if isa(line, Core.Expr) && line.head == :call
            if line.args[1].name == :sext_int && ci.ssavaluetypes[line_num] == Core.Int64
                push!(del_list[1], line_num)
                #arg 2 is the target type, arg 3 is the SSA, constant or arg
                if isa(line.args[3], Core.SSAValue)
                    push!(del_list[2], line.args[3].id)
                elseif isa(Core.SlotNumber)
                    error("slots, not currently supported")
                else #constant
                    error("constants, not currently supported")
                end
            end
        end
    end

    for (tgt, rpl) in zip(del_list[1], del_list[2])
        ci_ssa_replace!(ci, tgt, rpl)
    end
    for del in del_list[1]
        ci_delete!(ci, del)
    end
    return del_list
end

#CDFGArg struct - contains the arguments to a function
struct CDFGArg
    name::Symbol
    slotNum::Int
    type::DataType

    dataSuccs::Vector{Int} # [ssa val]
    ctrlSuccs::Vector{Int} #not sure how helpful this info is in its current state, might need to pull from CFG instead
end

#CDFGArg init - successors are not known at this point
function CDFGArg(name::Symbol, slotNum::Int, type::DataType)
    dataSuccs = Int[]
    ctrlSuccs = Int[]
    return CDFGArg(name, slotNum, type, dataSuccs, ctrlSuccs)
end

struct CDFGNode
    op::Any #narrow down the type later - define custom op type
    bb::Int #basic block number
    type::DataType #type of data output by node

    dataPreds::Array{Array{T,1} where T, 1} # [ssa val (int) or constant, type, position, literal or not(boolean)]
    dataSuccs::Vector{Int} # [ssa val] - may need to add position if there are multiple outputs - TODO work out how to ref generators
    #not sure how helpful this info is in its current state, might need to pull from CFG instead
    ctrlPreds::Vector{Int} #control info, basic blocks
    ctrlSuccs::Vector{Int}
end

#CDFG node constructors - successors are sorted when constructing the full CDFG
function CDFGNode(line::Core.Expr, linenum::Int64, bbnum::Int64, ssatypes::Array{Any, 1}, slottypes::Array{Any, 1}) #this includes gotoifnot, invokes, error throws etc. using slottyes might be inefficient for splats
    #vectors for links
    op= nothing
    bb= bbnum
    dp=[[],[],[],[]]
    ds=Int[]
    cp=[]
    cs=[]

    if line.head == :gotoifnot
        op = line.head
        if isa(line.args[1], Core.SSAValue) || isa(line.args[1], Core.SlotNumber)# this is the var for the conditional
            #line.args[1] = (line.args[1].id >= pos) ? Core.SSAValue(line.args[1].id + 1) : line.args[1]
            push!(dp[1], (isa(line.args[1], Core.SlotNumber) ? line.args[1] : line.args[1].id))
            push!(dp[2], (isa(line.args[1], Core.SlotNumber) ? slottypes[line.args[1].id] : ssatypes[line.args[1].id]))
            push!(dp[3], 1)
            push!(dp[4], (isa(line.args[1], Core.SlotNumber)))
        else #literals don't make sense for this node
            error("Unexpected data dependency for gotoifnot node")
        end
        #this is the target line to branch to, add to successor? control or data?
        #push!(cs, line.args[2])
        #line to branch to line.args[2] just an int
    elseif line.head == :invoke #nuke invoke nodes (collapse them to normal calls)
        op = line.args[2]
        try
            for (arg_n, arg) in enumerate(line.args[3:end])
                #this should ignore the first 2 args
                push!(dp[1], (isa(arg, Core.SSAValue) ? arg.id : arg))
                push!(dp[3], arg_n)
                push!(dp[4], !isa(arg, Core.SSAValue))
                if isa(arg, Core.SSAValue)
                    push!(dp[2], ssatypes[arg.id])
                elseif isa(arg, Core.SlotNumber) #add slot number references (inputs to function)
                    push!(dp[2], slottypes[arg.id])
                else #literal args - potentially dangerous to include everything else
                    push!(dp[2], typeof(arg))
                end
            end
        catch err
            if isa(err, Core.BoundsError)
                println("Invoke node has no args, this is fine.")
            else
                error(err)
            end
        end

    elseif line.head == :return
        op = line.head
        push!(dp[1], (isa(line.args[1], Core.SSAValue) ? line.args[1].id : line.args[1]))
        push!(dp[3], 1)
        push!(dp[4], !isa(line.args[1], Core.SSAValue))
        if isa(line.args[1], Core.SSAValue)
            push!(dp[2], ssatypes[line.args[1].id])
        elseif isa(line.args[1], Core.SlotNumber) #add slot number references (inputs to function)
            push!(dp[2], slottypes[line.args[1].id])
        else #literal args - potentially dangerous to include everything else
            push!(dp[2], typeof(line.args[1]))
        end

    elseif line.head == :call || line.head == :foreigncall
        op = line.args[1]
        try
            for (arg_n, arg) in enumerate(line.args[2:end])
                #this should ignore the first arg
                push!(dp[1], (isa(arg, Core.SSAValue) ? arg.id : arg))
                push!(dp[3], arg_n)
                push!(dp[4], !isa(arg, Core.SSAValue))
                if isa(arg, Core.SSAValue)
                    push!(dp[2], ssatypes[arg.id])
                elseif isa(arg, Core.SlotNumber) #add slot number references (inputs to function)
                    push!(dp[2], slottypes[arg.id])
                else #literal args - potentially dangerous to include everything else
                    push!(dp[2], typeof(arg))
                end
            end
        catch err
            if isa(err, Core.BoundsError)
                println("Call/foreigncall node has no args, this is fine.")
            else
                error(err)
            end
        end
    else
        #unknown experssion type
        error("CDFG has unknown expression type: ", line.head)
    end
    return CDFGNode(op, bb, ssatypes[linenum], dp, ds, cp, cs)
end

function CDFGNode(line::Core.PhiNode, linenum::Int, bbnum::Int64, ssatypes::Array{Any, 1}, slottypes::Array{Any, 1})
    op=:phi
    bb= bbnum
    dp=[[],[],[],[]]
    ds=Int[]
    cp=[]
    cs=[]

    for bb_end in line.edges #end of the basic blocks (last ssa val)
        push!(cp, bb_end)
    end

    for (val_n, val) in enumerate(line.values)
        push!(dp[1], (isa(val, Core.SSAValue) ? val.id : val))
        push!(dp[3], val_n)
        push!(dp[4], !isa(val, Core.SSAValue))
        if isa(val, Core.SSAValue)
            push!(dp[2], ssatypes[val.id])
        elseif isa(val, Core.SlotNumber) #add slot number references (inputs to function)
            push!(dp[2], slottypes[val.id])
        else #literal vals - potentially dangerous to include everything else
            push!(dp[2], typeof(val))
        end
    end

    #=for (val_n,val) in enumerate(line.values)
        if isa(val, Core.SSAValue)
            push!(dp[1], val.id)
            push!(dp[2], ssatypes[val.id])
            push!(dp[3], val_n)
        elseif isa(val, Core.SlotNumber) #add slot number references (inputs to function)
            push!(lits[1], val) #copy just incase
            push!(lits[2], slottypes[val.id])
            push!(lits[3], val_n)

        elseif !isa(val, Core.GlobalRef)
            push!(lits[1], val) #copy just incase
            push!(lits[2], typeof(val))
            push!(lits[3], val_n)
        end
    end=#
    return CDFGNode(op, bb, ssatypes[linenum], dp, ds, cp, cs)
end

function CDFGNode(line::Core.GotoNode, linenum::Int, bbnum::Int64, ssatypes::Array{Any, 1}, slottypes::Array{Any, 1})
    op=:goto
    bb= bbnum
    dp=[[],[],[],[]]
    ds=Int[]
    cp=[]
    cs=[]#[line.label]
    return CDFGNode(op, bb, ssatypes[linenum], dp, ds, cp, cs)
end

function CDFGNode(line::Nothing, linenum::Int, bbnum::Int64, ssatypes::Array{Any, 1}, slottypes::Array{Any, 1})
    op=:nth
    bb= bbnum
    dp=[[],[],[],[]]
    ds=Int[]
    cp=[]
    cs=[]
    return CDFGNode(op, bb, ssatypes[linenum], dp, ds, cp, cs)
end

#CDFG type - contains the function args, the nodes of the CDFG (each code line from )
struct CDFG
    args::Vector{CDFGArg}
    nodes::Vector{CDFGNode}
    cfg::Core.Compiler.CFG
end

#helper function to get the bb number
function get_bb_num(cfg::Core.Compiler.CFG, ssavalue::Int64)
    for (b_num, block) in enumerate(cfg.blocks)
        if ssavalue in block.stmts
            return b_num
        end
    end
    error("The ssavalue provided is not in a basic block")
end

#actual function to produce the CDFG
function get_cdfg(ci::CodeInfo)
    ci_inf = Core.Compiler.inflate_ir(ci)

    args = CDFGArg[CDFGArg(ci.slotnames[arg_num], arg_num, ci.slottypes[arg_num]) for arg_num in 2:length(ci_inf.argtypes)] #init arg nodes
    nodes = CDFGNode[CDFGNode(line, l_num, get_bb_num(ci_inf.cfg, l_num), ci.ssavaluetypes, ci.slottypes) for (l_num, line) in enumerate(ci.code)] #gen initial pred connections

    for (nn,node) in enumerate(nodes) #update missing successors
        for (dpv, lit_bool) in zip(node.dataPreds[1], node.dataPreds[4]) # update the succs of other blocks
            if lit_bool
                if isa(dpv, Core.SlotNumber)
                    push!(args[dpv.id-1].dataSuccs, nn)
                end
            else
                push!(nodes[dpv].dataSuccs, nn)
            end
        end

        for (cpv_num, cpv) in enumerate(node.ctrlPreds)
            push!(nodes[cpv].ctrlSuccs, nn) #TODO fix for nothing nodes

            if node.op == :phi #change the ssa values into BBs
                node.ctrlPreds[cpv_num] = get_bb_num(ci_inf.cfg, cpv)
            end
        end
        #might need to add control link updates here
    end

    return CDFG(args, nodes, ci_inf.cfg)
end

#graph visualisation tools
cfg_to_lightgraph(ci_p::Pair) = cfg_to_lightgraph(ci_p[1]::CodeInfo)

function cfg_to_lightgraph(ci::CodeInfo)
    ci_inf = Core.Compiler.inflate_ir(ci)
    cfg = LightGraphs.SimpleDiGraph(length(ci_inf.cfg.blocks))

    for (block_num, block ) in enumerate(ci_inf.cfg.blocks)
        map(x -> LightGraphs.add_edge!(cfg, block_num, x), block.succs)
    end

    return cfg
end

function cfg_to_lightgraph(cfg::Core.Compiler.CFG)
    cfg_lg = LightGraphs.SimpleDiGraph(length(cfg.blocks))

    for (block_num, block) in enumerate(cfg.blocks)
        map(x -> LightGraphs.add_edge!(cfg_lg, block_num, x), block.succs)
    end

    return cfg_lg
end

function disp_cdfg(cdfg::CDFG)
    disp_cdfg = SimpleDiGraph(length(cdfg.nodes))

    for (nn, node) in enumerate(cdfg.nodes)
        map(x -> LightGraphs.add_edge!(disp_cdfg, x, nn), node.dataPreds[1])
        map(x -> LightGraphs.add_edge!(disp_cdfg, x, nn), node.ctrlPreds)
    end

    return disp_cdfg
end

end # module
