using SSATools
using Test, LightGraphs

@testset "SSATools" begin

    @testset "function call graph" begin

    end

    @testset "ci_to_f" begin

        function pow(x, n)
            r = 1
            while n > 0
                n -= 1
                r *= x
            end
            return r
        end

        ci_pow_l = code_lowered(pow, Tuple{Int64, Int64})[1]
        plf = SSATools.ci_to_f(ci_pow_l, 2)

        @test plf(3,2) == 9

        ci_pow_t = code_typed(pow, Tuple{Int64, Int64})[1]
        ptf = SSATools.ci_to_f(ci_pow_t, 2)

        @test ptf(3,2) == 9

        m_v_mult(M::AbstractMatrix{Int64}, v::AbstractVector{Int64}) = M*v
        ci_mv_t = code_typed(m_v_mult, Tuple{Array{Int64,2}, Array{Int64,1}})[1]
        mvf = SSATools.ci_to_f(ci_mv_t, 2)

        @test mvf([1 2; 3 4], [0; -1]) == [-2; -4]

        function m_m_mult(M1::AbstractMatrix, M2::AbstractMatrix)
                n, m = size(M2)
                res=[]
                for i in 1:n
                        push!(res, m_v_mult(M1,M2[:,i]))
                end
                return hcat(res...) #[ m_v_mult(M1,M2[:,i]) for i in 1:n]...)
        end

        ci_mm_t = code_typed(m_m_mult, Tuple{Array{Int64,2}, Array{Int64,2}})[1]
        mmf = SSATools.ci_to_f(ci_mm_t, 2)

        @test mmf([1 2; 3 4], [0 1; -1 0]) == [-2 1; -4 3]

        function foo3(a::Int64)
            result = 0
            for i in 1:a
                    result = result + 1
            end
            return result
        end

        f3_t = code_typed(foo3, Tuple{Int64})[1]
        f3f = SSATools.ci_to_f(f3_t, 1)

        @test f3f(6) == 6

    end

    @testset "Control Flow Graph" begin

        function foo_maths(x::Int64)
                a = x^6 + 3x^3
                if a % 3 == 0
                        a -= (5x^2 - x + 512)
                else
                        a += (5x^2 - x + 512)
                end

        end

        fm_tir = code_typed(foo_maths, Tuple{Int64})[1]
        fm_cfg = SSATools.disp_cfg(fm_tir)
        fm_cfg_v = LightGraphs.SimpleDiGraph(3)
        LightGraphs.add_edge!(fm_cfg_v, 1, 2)
        LightGraphs.add_edge!(fm_cfg_v, 1, 3)

        @test fm_cfg == fm_cfg_v

        function jpow(x::Int64, n::Int64) #basic power function
                r = 1
                while n > 0
                        n -= 1
                        r *= x
                end
                return r
        end

        jp_tir = code_typed(jpow, Tuple{Int64, Int64})[1]
        jp_cfg = SSATools.disp_cfg(jp_tir)

        jp_cfg_v = LightGraphs.SimpleDiGraph(4)
        LightGraphs.add_edge!(jp_cfg_v, 1, 2)
        LightGraphs.add_edge!(jp_cfg_v, 2, 3)
        LightGraphs.add_edge!(jp_cfg_v, 3, 2)
        LightGraphs.add_edge!(jp_cfg_v, 2, 4)

        @test jp_cfg == jp_cfg_v
    end

    @testset "Control Data Flow Graph" begin

    end
end
