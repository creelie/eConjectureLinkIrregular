# verify_linkirr.jl -- checks for "Link-irregular tournaments exist for every order at least six".
#
#  * T_6, T_7 (the paper's arcs) and T_{n+2} = T_n^+ for n + 2 <= 22: tournament, no source or
#    sink, links pairwise non-isomorphic (backtracking over score classes, a third implementation);
#  * Table 1;
#  * the marked vertex of every link T_n - v (v old) is t;
#  * the remark: from T_7, the links of T_n have pairwise different score sequences, odd n <= 101.
# Prints "ALL OK" when every check passes.

failed = false
function check(c, msg)
    global failed
    println(c ? "ok   " : "FAIL ", msg)
    c || (failed = true)
end

function fromarcs(n, arcs)
    a = zeros(Int, n, n)
    for i in 1:n, j in 1:i-1
        a[i, j] = 1
    end
    for (i, j) in arcs
        a[i, j] = 1; a[j, i] = 0
    end
    a
end

const T6 = fromarcs(6, [(1,2),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5),(2,6),(3,4),(3,6),(4,5),(4,6),(5,3),(6,1),(6,5)])
const T7 = fromarcs(7, [(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,4),(2,5),(2,6),(2,7),(3,4),(3,5),(3,7),
                        (4,5),(4,6),(4,7),(5,6),(6,3),(7,1),(7,5),(7,6)])

scores(a) = vec(sum(a, dims = 2))
link(a, v) = (idx = [u for u in 1:size(a, 1) if u != v]; a[idx, idx])
istournament(a) = all(a[i, i] == 0 for i in axes(a, 1)) &&
                  all(a[i, j] + a[j, i] == 1 for i in axes(a, 1) for j in i+1:size(a, 1))
nosourcesink(a) = all(0 .< scores(a) .< size(a, 1) - 1)

function plus(a)
    n = size(a, 1)
    p = zeros(Int, n + 2, n + 2)
    p[1:n, 1:n] = a
    p[n+1, 1:n] .= 1          # s beats every old vertex
    p[1:n, n+2] .= 1          # every old vertex beats t
    p[n+2, n+1] = 1           # t -> s
    p
end

function isiso(x, y)
    n = size(x, 1)
    sx, sy = scores(x), scores(y)
    sort(sx) == sort(sy) || return false
    img = zeros(Int, n); used = falses(n)
    function ext(i)
        i > n && return true
        for b in 1:n
            (used[b] || sy[b] != sx[i]) && continue
            all(x[i, j] == y[b, img[j]] && x[j, i] == y[img[j], b] for j in 1:i-1) || continue
            img[i] = b; used[b] = true
            ext(i + 1) && return true
            used[b] = false
        end
        false
    end
    ext(1)
end

function linkirregular(a)
    n = size(a, 1)
    L = [link(a, v) for v in 1:n]
    !any(isiso(L[v], L[w]) for v in 1:n for w in v+1:n)
end

check(istournament(T6) && istournament(T7), "T_6 and T_7 are tournaments")
check(scores(T6) == [4, 4, 2, 2, 1, 2] && scores(T7) == [5, 5, 3, 3, 1, 1, 3], "scores of T_6 and T_7")
tab6 = [[1,1,2,2,4], [1,2,2,2,3], [0,2,2,3,3], [1,1,2,3,3], [1,1,2,3,3], [1,1,1,3,4]]
tab7 = [[1,1,2,3,3,5], [1,1,3,3,3,4], [0,1,3,3,4,4], [1,1,2,3,4,4], [1,2,2,2,4,4], [0,2,2,3,4,4], [1,1,2,2,4,5]]
check([sort(scores(link(T6, v))) for v in 1:6] == tab6 && [sort(scores(link(T7, v))) for v in 1:7] == tab7, "Table 1")

T = Dict(6 => T6, 7 => T7)
for n in 8:22
    T[n] = plus(T[n-2])
end
check(all(istournament(T[n]) && nosourcesink(T[n]) && linkirregular(T[n]) for n in 6:22),
      "T_n is a link-irregular tournament with neither a source nor a sink, 6 <= n <= 22")

ok = true
for n in 8:22
    m = n - 2
    for v in 1:m
        l = link(T[n], v)
        s = scores(l)
        marked = [y for y in 1:n-1 if s[y] == 1 && all(s[z] == m - 1 for z in 1:n-1 if l[y, z] == 1)]
        global ok &= marked == [n - 1]      # t is the last vertex of T_n - v
    end
end
check(ok, "the only marked vertex of each link T_n - v, v old, is t (8 <= n <= 22)")

a = T7; ok = true
for n in 7:2:101
    global ok &= length(Set(sort(scores(link(a, v))) for v in 1:n)) == n
    global a = plus(a)
end
check(ok, "from T_7: the links of T_n have pairwise different score sequences for odd n <= 101")

println(failed ? "SOME CHECKS FAILED" : "ALL OK")
exit(failed ? 1 : 0)
