module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.RepresentativeChecks.Obstructions.CachedActions
import Mathlib.Tactic.FinCases

/-!
# Prime-order obstructions for Held representatives 2048 through 2303

For every nonlocal row, kernel reduction verifies a nontrivial prime orbit
of a word in the actual marked generators and representative. The orbit
lemma then constructs an element of that prime order in their generated
subgroup. The cached marked actions are proved equal to the originals.

Source: `../source/orbits.json`, generated from the unchanged ATLAS carrier
by `../source/search_orbits.py`. Emitted by `source/generate.py`; the generator
and JSON are not trusted proof inputs.
-/

namespace Held.LocalPairs.PairCoverage.SylowOvergroups.RepresentativeVerification

set_option Elab.async false

set_option maxRecDepth 16000 in
private theorem obstruction_2048 : HasPrimeObstruction (representative 2048) := by
  apply obstruction_of_cachedAction 2048 [5] 7 1
    (by decide) (by decide) (by decide) 50
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2049 : HasPrimeObstruction (representative 2049) := by
  apply obstruction_of_cachedAction 2049 [5] 7 1
    (by decide) (by decide) (by decide) 88
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2050 : HasPrimeObstruction (representative 2050) := by
  apply obstruction_of_cachedAction 2050 [5] 7 1
    (by decide) (by decide) (by decide) 16
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2051 : HasPrimeObstruction (representative 2051) := by
  apply obstruction_of_cachedAction 2051 [5] 7 1
    (by decide) (by decide) (by decide) 5
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2052 : HasPrimeObstruction (representative 2052) := by
  apply obstruction_of_cachedAction 2052 [5, 1] 5 1
    (by decide) (by decide) (by decide) 22
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2053 : HasPrimeObstruction (representative 2053) := by
  apply obstruction_of_cachedAction 2053 [5] 7 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2054 : HasPrimeObstruction (representative 2054) := by
  apply obstruction_of_cachedAction 2054 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2055 : HasPrimeObstruction (representative 2055) := by
  apply obstruction_of_cachedAction 2055 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2056 : HasPrimeObstruction (representative 2056) := by
  apply obstruction_of_cachedAction 2056 [5, 1] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2057 : HasPrimeObstruction (representative 2057) := by
  apply obstruction_of_cachedAction 2057 [5] 5 1
    (by decide) (by decide) (by decide) 26
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2058 : HasPrimeObstruction (representative 2058) := by
  apply obstruction_of_cachedAction 2058 [5] 5 1
    (by decide) (by decide) (by decide) 11
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2059 : HasPrimeObstruction (representative 2059) := by
  apply obstruction_of_cachedAction 2059 [5, 3] 7 1
    (by decide) (by decide) (by decide) 2
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2060 : HasPrimeObstruction (representative 2060) := by
  apply obstruction_of_cachedAction 2060 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2061 : HasPrimeObstruction (representative 2061) := by
  apply obstruction_of_cachedAction 2061 [5] 7 1
    (by decide) (by decide) (by decide) 108
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2062 : HasPrimeObstruction (representative 2062) := by
  apply obstruction_of_cachedAction 2062 [5] 5 1
    (by decide) (by decide) (by decide) 128
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2063 : HasPrimeObstruction (representative 2063) := by
  apply obstruction_of_cachedAction 2063 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2064 : HasPrimeObstruction (representative 2064) := by
  apply obstruction_of_cachedAction 2064 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2065 : HasPrimeObstruction (representative 2065) := by
  apply obstruction_of_cachedAction 2065 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2066 : HasPrimeObstruction (representative 2066) := by
  apply obstruction_of_cachedAction 2066 [5] 7 1
    (by decide) (by decide) (by decide) 32
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2067 : HasPrimeObstruction (representative 2067) := by
  apply obstruction_of_cachedAction 2067 [5, 1] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2068 : HasPrimeObstruction (representative 2068) := by
  apply obstruction_of_cachedAction 2068 [5, 3] 7 1
    (by decide) (by decide) (by decide) 17
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2069 : HasPrimeObstruction (representative 2069) := by
  apply obstruction_of_cachedAction 2069 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2070 : HasPrimeObstruction (representative 2070) := by
  apply obstruction_of_cachedAction 2070 [5] 7 1
    (by decide) (by decide) (by decide) 13
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2071 : HasPrimeObstruction (representative 2071) := by
  apply obstruction_of_cachedAction 2071 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2072 : HasPrimeObstruction (representative 2072) := by
  apply obstruction_of_cachedAction 2072 [5] 7 1
    (by decide) (by decide) (by decide) 48
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2073 : HasPrimeObstruction (representative 2073) := by
  apply obstruction_of_cachedAction 2073 [5] 5 1
    (by decide) (by decide) (by decide) 38
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2074 : HasPrimeObstruction (representative 2074) := by
  apply obstruction_of_cachedAction 2074 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2075 : HasPrimeObstruction (representative 2075) := by
  apply obstruction_of_cachedAction 2075 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2076 : HasPrimeObstruction (representative 2076) := by
  apply obstruction_of_cachedAction 2076 [5, 3] 5 1
    (by decide) (by decide) (by decide) 39
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2077 : HasPrimeObstruction (representative 2077) := by
  apply obstruction_of_cachedAction 2077 [5, 4] 7 1
    (by decide) (by decide) (by decide) 5
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2078 : HasPrimeObstruction (representative 2078) := by
  apply obstruction_of_cachedAction 2078 [5] 5 1
    (by decide) (by decide) (by decide) 7
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2079 : HasPrimeObstruction (representative 2079) := by
  apply obstruction_of_cachedAction 2079 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2080 : HasPrimeObstruction (representative 2080) := by
  apply obstruction_of_cachedAction 2080 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2081 : HasPrimeObstruction (representative 2081) := by
  apply obstruction_of_cachedAction 2081 [5, 1] 7 1
    (by decide) (by decide) (by decide) 301
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2082 : HasPrimeObstruction (representative 2082) := by
  apply obstruction_of_cachedAction 2082 [5, 4] 5 1
    (by decide) (by decide) (by decide) 144
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2083 : HasPrimeObstruction (representative 2083) := by
  apply obstruction_of_cachedAction 2083 [5] 7 1
    (by decide) (by decide) (by decide) 9
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2084 : HasPrimeObstruction (representative 2084) := by
  apply obstruction_of_cachedAction 2084 [5, 2] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2085 : HasPrimeObstruction (representative 2085) := by
  apply obstruction_of_cachedAction 2085 [5, 2] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2086 : HasPrimeObstruction (representative 2086) := by
  apply obstruction_of_cachedAction 2086 [5] 5 1
    (by decide) (by decide) (by decide) 48
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2087 : HasPrimeObstruction (representative 2087) := by
  apply obstruction_of_cachedAction 2087 [5, 1] 7 1
    (by decide) (by decide) (by decide) 26
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2088 : HasPrimeObstruction (representative 2088) := by
  apply obstruction_of_cachedAction 2088 [5] 5 1
    (by decide) (by decide) (by decide) 17
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2089 : HasPrimeObstruction (representative 2089) := by
  apply obstruction_of_cachedAction 2089 [5] 5 1
    (by decide) (by decide) (by decide) 26
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2090 : HasPrimeObstruction (representative 2090) := by
  apply obstruction_of_cachedAction 2090 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2091 : HasPrimeObstruction (representative 2091) := by
  apply obstruction_of_cachedAction 2091 [5] 5 1
    (by decide) (by decide) (by decide) 20
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2092 : HasPrimeObstruction (representative 2092) := by
  apply obstruction_of_cachedAction 2092 [5, 1] 7 1
    (by decide) (by decide) (by decide) 302
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2093 : HasPrimeObstruction (representative 2093) := by
  apply obstruction_of_cachedAction 2093 [5] 7 1
    (by decide) (by decide) (by decide) 2
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2094 : HasPrimeObstruction (representative 2094) := by
  apply obstruction_of_cachedAction 2094 [5] 7 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2095 : HasPrimeObstruction (representative 2095) := by
  apply obstruction_of_cachedAction 2095 [5] 7 1
    (by decide) (by decide) (by decide) 120
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2096 : HasPrimeObstruction (representative 2096) := by
  apply obstruction_of_cachedAction 2096 [5, 1] 5 1
    (by decide) (by decide) (by decide) 18
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2097 : HasPrimeObstruction (representative 2097) := by
  apply obstruction_of_cachedAction 2097 [5] 7 1
    (by decide) (by decide) (by decide) 30
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2098 : HasPrimeObstruction (representative 2098) := by
  apply obstruction_of_cachedAction 2098 [5, 3] 5 1
    (by decide) (by decide) (by decide) 19
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2099 : HasPrimeObstruction (representative 2099) := by
  apply obstruction_of_cachedAction 2099 [5] 7 1
    (by decide) (by decide) (by decide) 1
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2100 : HasPrimeObstruction (representative 2100) := by
  apply obstruction_of_cachedAction 2100 [5] 7 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2101 : HasPrimeObstruction (representative 2101) := by
  apply obstruction_of_cachedAction 2101 [5, 4] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2102 : HasPrimeObstruction (representative 2102) := by
  apply obstruction_of_cachedAction 2102 [5, 2] 7 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2103 : HasPrimeObstruction (representative 2103) := by
  apply obstruction_of_cachedAction 2103 [5, 2] 7 1
    (by decide) (by decide) (by decide) 24
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2104 : HasPrimeObstruction (representative 2104) := by
  apply obstruction_of_cachedAction 2104 [5] 7 1
    (by decide) (by decide) (by decide) 76
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2105 : HasPrimeObstruction (representative 2105) := by
  apply obstruction_of_cachedAction 2105 [5, 2] 7 1
    (by decide) (by decide) (by decide) 8
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2106 : HasPrimeObstruction (representative 2106) := by
  apply obstruction_of_cachedAction 2106 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2107 : HasPrimeObstruction (representative 2107) := by
  apply obstruction_of_cachedAction 2107 [5] 7 1
    (by decide) (by decide) (by decide) 10
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2108 : HasPrimeObstruction (representative 2108) := by
  apply obstruction_of_cachedAction 2108 [5] 7 1
    (by decide) (by decide) (by decide) 89
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2109 : HasPrimeObstruction (representative 2109) := by
  apply obstruction_of_cachedAction 2109 [5, 1] 7 1
    (by decide) (by decide) (by decide) 28
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2110 : HasPrimeObstruction (representative 2110) := by
  apply obstruction_of_cachedAction 2110 [5] 7 1
    (by decide) (by decide) (by decide) 108
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2111 : HasPrimeObstruction (representative 2111) := by
  apply obstruction_of_cachedAction 2111 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2112 : HasPrimeObstruction (representative 2112) := by
  apply obstruction_of_cachedAction 2112 [5] 7 1
    (by decide) (by decide) (by decide) 112
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2113 : HasPrimeObstruction (representative 2113) := by
  apply obstruction_of_cachedAction 2113 [5] 7 1
    (by decide) (by decide) (by decide) 81
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2114 : HasPrimeObstruction (representative 2114) := by
  apply obstruction_of_cachedAction 2114 [5, 2] 7 1
    (by decide) (by decide) (by decide) 1
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2115 : HasPrimeObstruction (representative 2115) := by
  apply obstruction_of_cachedAction 2115 [5] 7 1
    (by decide) (by decide) (by decide) 35
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2116 : HasPrimeObstruction (representative 2116) := by
  apply obstruction_of_cachedAction 2116 [5] 7 1
    (by decide) (by decide) (by decide) 2
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2117 : HasPrimeObstruction (representative 2117) := by
  apply obstruction_of_cachedAction 2117 [5, 1] 7 1
    (by decide) (by decide) (by decide) 24
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2118 : HasPrimeObstruction (representative 2118) := by
  apply obstruction_of_cachedAction 2118 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2119 : HasPrimeObstruction (representative 2119) := by
  apply obstruction_of_cachedAction 2119 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2120 : HasPrimeObstruction (representative 2120) := by
  apply obstruction_of_cachedAction 2120 [5, 2] 5 1
    (by decide) (by decide) (by decide) 167
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2121 : HasPrimeObstruction (representative 2121) := by
  apply obstruction_of_cachedAction 2121 [5] 7 1
    (by decide) (by decide) (by decide) 5
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2122 : HasPrimeObstruction (representative 2122) := by
  apply obstruction_of_cachedAction 2122 [5, 4] 7 1
    (by decide) (by decide) (by decide) 172
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2123 : HasPrimeObstruction (representative 2123) := by
  apply obstruction_of_cachedAction 2123 [5] 5 1
    (by decide) (by decide) (by decide) 51
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2124 : HasPrimeObstruction (representative 2124) := by
  apply obstruction_of_cachedAction 2124 [5, 3] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2125 : HasPrimeObstruction (representative 2125) := by
  apply obstruction_of_cachedAction 2125 [5, 1] 7 1
    (by decide) (by decide) (by decide) 18
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2126 : HasPrimeObstruction (representative 2126) := by
  apply obstruction_of_cachedAction 2126 [5] 7 1
    (by decide) (by decide) (by decide) 2
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2127 : HasPrimeObstruction (representative 2127) := by
  apply obstruction_of_cachedAction 2127 [5, 1] 5 1
    (by decide) (by decide) (by decide) 5
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2128 : HasPrimeObstruction (representative 2128) := by
  apply obstruction_of_cachedAction 2128 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2129 : HasPrimeObstruction (representative 2129) := by
  apply obstruction_of_cachedAction 2129 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2130 : HasPrimeObstruction (representative 2130) := by
  apply obstruction_of_cachedAction 2130 [5] 7 1
    (by decide) (by decide) (by decide) 74
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2131 : HasPrimeObstruction (representative 2131) := by
  apply obstruction_of_cachedAction 2131 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2132 : HasPrimeObstruction (representative 2132) := by
  apply obstruction_of_cachedAction 2132 [5] 7 1
    (by decide) (by decide) (by decide) 203
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2133 : HasPrimeObstruction (representative 2133) := by
  apply obstruction_of_cachedAction 2133 [5] 5 1
    (by decide) (by decide) (by decide) 15
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2134 : HasPrimeObstruction (representative 2134) := by
  apply obstruction_of_cachedAction 2134 [5] 7 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2135 : HasPrimeObstruction (representative 2135) := by
  apply obstruction_of_cachedAction 2135 [5] 7 1
    (by decide) (by decide) (by decide) 62
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2136 : HasPrimeObstruction (representative 2136) := by
  apply obstruction_of_cachedAction 2136 [5] 5 1
    (by decide) (by decide) (by decide) 3
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2137 : HasPrimeObstruction (representative 2137) := by
  apply obstruction_of_cachedAction 2137 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2138 : HasPrimeObstruction (representative 2138) := by
  apply obstruction_of_cachedAction 2138 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2139 : HasPrimeObstruction (representative 2139) := by
  apply obstruction_of_cachedAction 2139 [5, 1] 7 1
    (by decide) (by decide) (by decide) 55
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2140 : HasPrimeObstruction (representative 2140) := by
  apply obstruction_of_cachedAction 2140 [5] 7 1
    (by decide) (by decide) (by decide) 51
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2141 : HasPrimeObstruction (representative 2141) := by
  apply obstruction_of_cachedAction 2141 [5] 7 1
    (by decide) (by decide) (by decide) 18
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2142 : HasPrimeObstruction (representative 2142) := by
  apply obstruction_of_cachedAction 2142 [5, 4] 5 1
    (by decide) (by decide) (by decide) 22
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2143 : HasPrimeObstruction (representative 2143) := by
  apply obstruction_of_cachedAction 2143 [5, 4] 7 1
    (by decide) (by decide) (by decide) 81
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2144 : HasPrimeObstruction (representative 2144) := by
  apply obstruction_of_cachedAction 2144 [5] 5 1
    (by decide) (by decide) (by decide) 8
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2145 : HasPrimeObstruction (representative 2145) := by
  apply obstruction_of_cachedAction 2145 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2146 : HasPrimeObstruction (representative 2146) := by
  apply obstruction_of_cachedAction 2146 [5] 7 1
    (by decide) (by decide) (by decide) 212
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2147 : HasPrimeObstruction (representative 2147) := by
  apply obstruction_of_cachedAction 2147 [5] 7 1
    (by decide) (by decide) (by decide) 47
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2148 : HasPrimeObstruction (representative 2148) := by
  apply obstruction_of_cachedAction 2148 [5] 7 1
    (by decide) (by decide) (by decide) 5
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2149 : HasPrimeObstruction (representative 2149) := by
  apply obstruction_of_cachedAction 2149 [5] 5 1
    (by decide) (by decide) (by decide) 116
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2150 : HasPrimeObstruction (representative 2150) := by
  apply obstruction_of_cachedAction 2150 [5] 7 1
    (by decide) (by decide) (by decide) 3
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2151 : HasPrimeObstruction (representative 2151) := by
  apply obstruction_of_cachedAction 2151 [5] 7 1
    (by decide) (by decide) (by decide) 82
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2152 : HasPrimeObstruction (representative 2152) := by
  apply obstruction_of_cachedAction 2152 [5] 7 1
    (by decide) (by decide) (by decide) 3
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2153 : HasPrimeObstruction (representative 2153) := by
  apply obstruction_of_cachedAction 2153 [5, 3] 7 1
    (by decide) (by decide) (by decide) 8
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2154 : HasPrimeObstruction (representative 2154) := by
  apply obstruction_of_cachedAction 2154 [5] 7 1
    (by decide) (by decide) (by decide) 50
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2155 : HasPrimeObstruction (representative 2155) := by
  apply obstruction_of_cachedAction 2155 [5] 7 1
    (by decide) (by decide) (by decide) 47
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2156 : HasPrimeObstruction (representative 2156) := by
  apply obstruction_of_cachedAction 2156 [5] 7 1
    (by decide) (by decide) (by decide) 1
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2157 : HasPrimeObstruction (representative 2157) := by
  apply obstruction_of_cachedAction 2157 [5] 7 1
    (by decide) (by decide) (by decide) 104
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2158 : HasPrimeObstruction (representative 2158) := by
  apply obstruction_of_cachedAction 2158 [5] 7 1
    (by decide) (by decide) (by decide) 1
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2159 : HasPrimeObstruction (representative 2159) := by
  apply obstruction_of_cachedAction 2159 [5] 7 1
    (by decide) (by decide) (by decide) 6
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2160 : HasPrimeObstruction (representative 2160) := by
  apply obstruction_of_cachedAction 2160 [5, 1] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2161 : HasPrimeObstruction (representative 2161) := by
  apply obstruction_of_cachedAction 2161 [5, 1] 7 1
    (by decide) (by decide) (by decide) 22
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2162 : HasPrimeObstruction (representative 2162) := by
  apply obstruction_of_cachedAction 2162 [5] 7 1
    (by decide) (by decide) (by decide) 4
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2163 : HasPrimeObstruction (representative 2163) := by
  apply obstruction_of_cachedAction 2163 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2164 : HasPrimeObstruction (representative 2164) := by
  apply obstruction_of_cachedAction 2164 [5, 4, 3, 5, 3] 7 1
    (by decide) (by decide) (by decide) 13
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2165 : HasPrimeObstruction (representative 2165) := by
  apply obstruction_of_cachedAction 2165 [5, 3] 5 1
    (by decide) (by decide) (by decide) 5
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2166 : HasPrimeObstruction (representative 2166) := by
  apply obstruction_of_cachedAction 2166 [5, 2] 7 1
    (by decide) (by decide) (by decide) 8
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2167 : HasPrimeObstruction (representative 2167) := by
  apply obstruction_of_cachedAction 2167 [5] 7 1
    (by decide) (by decide) (by decide) 1
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2168 : HasPrimeObstruction (representative 2168) := by
  apply obstruction_of_cachedAction 2168 [5] 7 1
    (by decide) (by decide) (by decide) 91
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2169 : HasPrimeObstruction (representative 2169) := by
  apply obstruction_of_cachedAction 2169 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2170 : HasPrimeObstruction (representative 2170) := by
  apply obstruction_of_cachedAction 2170 [5] 7 1
    (by decide) (by decide) (by decide) 57
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2171 : HasPrimeObstruction (representative 2171) := by
  apply obstruction_of_cachedAction 2171 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2172 : HasPrimeObstruction (representative 2172) := by
  apply obstruction_of_cachedAction 2172 [5, 1] 5 1
    (by decide) (by decide) (by decide) 7
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2173 : HasPrimeObstruction (representative 2173) := by
  apply obstruction_of_cachedAction 2173 [5] 5 1
    (by decide) (by decide) (by decide) 49
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2174 : HasPrimeObstruction (representative 2174) := by
  apply obstruction_of_cachedAction 2174 [5] 7 1
    (by decide) (by decide) (by decide) 47
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2175 : HasPrimeObstruction (representative 2175) := by
  apply obstruction_of_cachedAction 2175 [5] 5 1
    (by decide) (by decide) (by decide) 63
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2176 : HasPrimeObstruction (representative 2176) := by
  apply obstruction_of_cachedAction 2176 [5] 7 1
    (by decide) (by decide) (by decide) 23
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2177 : HasPrimeObstruction (representative 2177) := by
  apply obstruction_of_cachedAction 2177 [5] 5 1
    (by decide) (by decide) (by decide) 67
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2178 : HasPrimeObstruction (representative 2178) := by
  apply obstruction_of_cachedAction 2178 [5] 5 1
    (by decide) (by decide) (by decide) 41
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2179 : HasPrimeObstruction (representative 2179) := by
  apply obstruction_of_cachedAction 2179 [5, 4] 5 1
    (by decide) (by decide) (by decide) 21
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2180 : HasPrimeObstruction (representative 2180) := by
  apply obstruction_of_cachedAction 2180 [5] 5 1
    (by decide) (by decide) (by decide) 8
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2181 : HasPrimeObstruction (representative 2181) := by
  apply obstruction_of_cachedAction 2181 [5] 5 1
    (by decide) (by decide) (by decide) 6
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2182 : HasPrimeObstruction (representative 2182) := by
  apply obstruction_of_cachedAction 2182 [5, 2] 5 1
    (by decide) (by decide) (by decide) 19
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2183 : HasPrimeObstruction (representative 2183) := by
  apply obstruction_of_cachedAction 2183 [5] 5 1
    (by decide) (by decide) (by decide) 9
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2184 : HasPrimeObstruction (representative 2184) := by
  apply obstruction_of_cachedAction 2184 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2185 : HasPrimeObstruction (representative 2185) := by
  apply obstruction_of_cachedAction 2185 [5] 5 1
    (by decide) (by decide) (by decide) 4
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2186 : HasPrimeObstruction (representative 2186) := by
  apply obstruction_of_cachedAction 2186 [5, 1] 7 1
    (by decide) (by decide) (by decide) 17
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2187 : HasPrimeObstruction (representative 2187) := by
  apply obstruction_of_cachedAction 2187 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2188 : HasPrimeObstruction (representative 2188) := by
  apply obstruction_of_cachedAction 2188 [5] 7 1
    (by decide) (by decide) (by decide) 38
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2189 : HasPrimeObstruction (representative 2189) := by
  apply obstruction_of_cachedAction 2189 [5] 5 1
    (by decide) (by decide) (by decide) 52
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2190 : HasPrimeObstruction (representative 2190) := by
  apply obstruction_of_cachedAction 2190 [5] 7 1
    (by decide) (by decide) (by decide) 10
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2191 : HasPrimeObstruction (representative 2191) := by
  apply obstruction_of_cachedAction 2191 [5, 1] 7 1
    (by decide) (by decide) (by decide) 134
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2192 : HasPrimeObstruction (representative 2192) := by
  apply obstruction_of_cachedAction 2192 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2193 : HasPrimeObstruction (representative 2193) := by
  apply obstruction_of_cachedAction 2193 [5] 7 1
    (by decide) (by decide) (by decide) 273
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2194 : HasPrimeObstruction (representative 2194) := by
  apply obstruction_of_cachedAction 2194 [5] 7 1
    (by decide) (by decide) (by decide) 10
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2195 : HasPrimeObstruction (representative 2195) := by
  apply obstruction_of_cachedAction 2195 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2196 : HasPrimeObstruction (representative 2196) := by
  apply obstruction_of_cachedAction 2196 [5] 7 1
    (by decide) (by decide) (by decide) 2
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2197 : HasPrimeObstruction (representative 2197) := by
  apply obstruction_of_cachedAction 2197 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2198 : HasPrimeObstruction (representative 2198) := by
  apply obstruction_of_cachedAction 2198 [5, 1] 5 1
    (by decide) (by decide) (by decide) 12
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2199 : HasPrimeObstruction (representative 2199) := by
  apply obstruction_of_cachedAction 2199 [5, 2] 5 1
    (by decide) (by decide) (by decide) 71
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2200 : HasPrimeObstruction (representative 2200) := by
  apply obstruction_of_cachedAction 2200 [5, 2] 7 1
    (by decide) (by decide) (by decide) 16
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2201 : HasPrimeObstruction (representative 2201) := by
  apply obstruction_of_cachedAction 2201 [5] 7 1
    (by decide) (by decide) (by decide) 10
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2202 : HasPrimeObstruction (representative 2202) := by
  apply obstruction_of_cachedAction 2202 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2203 : HasPrimeObstruction (representative 2203) := by
  apply obstruction_of_cachedAction 2203 [5, 3] 5 1
    (by decide) (by decide) (by decide) 30
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2204 : HasPrimeObstruction (representative 2204) := by
  apply obstruction_of_cachedAction 2204 [5] 7 1
    (by decide) (by decide) (by decide) 100
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2205 : HasPrimeObstruction (representative 2205) := by
  apply obstruction_of_cachedAction 2205 [5] 7 1
    (by decide) (by decide) (by decide) 17
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2206 : HasPrimeObstruction (representative 2206) := by
  apply obstruction_of_cachedAction 2206 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2207 : HasPrimeObstruction (representative 2207) := by
  apply obstruction_of_cachedAction 2207 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2208 : HasPrimeObstruction (representative 2208) := by
  apply obstruction_of_cachedAction 2208 [5, 3] 5 1
    (by decide) (by decide) (by decide) 10
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2209 : HasPrimeObstruction (representative 2209) := by
  apply obstruction_of_cachedAction 2209 [5] 5 1
    (by decide) (by decide) (by decide) 10
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2210 : HasPrimeObstruction (representative 2210) := by
  apply obstruction_of_cachedAction 2210 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2211 : HasPrimeObstruction (representative 2211) := by
  apply obstruction_of_cachedAction 2211 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2212 : HasPrimeObstruction (representative 2212) := by
  apply obstruction_of_cachedAction 2212 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2213 : HasPrimeObstruction (representative 2213) := by
  apply obstruction_of_cachedAction 2213 [5, 4] 5 1
    (by decide) (by decide) (by decide) 31
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2214 : HasPrimeObstruction (representative 2214) := by
  apply obstruction_of_cachedAction 2214 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2215 : HasPrimeObstruction (representative 2215) := by
  apply obstruction_of_cachedAction 2215 [5] 7 1
    (by decide) (by decide) (by decide) 40
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2216 : HasPrimeObstruction (representative 2216) := by
  apply obstruction_of_cachedAction 2216 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2217 : HasPrimeObstruction (representative 2217) := by
  apply obstruction_of_cachedAction 2217 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2218 : HasPrimeObstruction (representative 2218) := by
  apply obstruction_of_cachedAction 2218 [5] 7 1
    (by decide) (by decide) (by decide) 20
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2219 : HasPrimeObstruction (representative 2219) := by
  apply obstruction_of_cachedAction 2219 [5] 7 1
    (by decide) (by decide) (by decide) 14
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2220 : HasPrimeObstruction (representative 2220) := by
  apply obstruction_of_cachedAction 2220 [5, 1] 7 1
    (by decide) (by decide) (by decide) 55
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2221 : HasPrimeObstruction (representative 2221) := by
  apply obstruction_of_cachedAction 2221 [5] 7 1
    (by decide) (by decide) (by decide) 44
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2222 : HasPrimeObstruction (representative 2222) := by
  apply obstruction_of_cachedAction 2222 [5] 7 1
    (by decide) (by decide) (by decide) 22
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2223 : HasPrimeObstruction (representative 2223) := by
  apply obstruction_of_cachedAction 2223 [5] 5 1
    (by decide) (by decide) (by decide) 1
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2224 : HasPrimeObstruction (representative 2224) := by
  apply obstruction_of_cachedAction 2224 [5] 7 1
    (by decide) (by decide) (by decide) 4
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2225 : HasPrimeObstruction (representative 2225) := by
  apply obstruction_of_cachedAction 2225 [5] 7 1
    (by decide) (by decide) (by decide) 14
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2226 : HasPrimeObstruction (representative 2226) := by
  apply obstruction_of_cachedAction 2226 [5, 1] 5 1
    (by decide) (by decide) (by decide) 9
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2227 : HasPrimeObstruction (representative 2227) := by
  apply obstruction_of_cachedAction 2227 [5, 1] 7 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2228 : HasPrimeObstruction (representative 2228) := by
  apply obstruction_of_cachedAction 2228 [5] 7 1
    (by decide) (by decide) (by decide) 25
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2229 : HasPrimeObstruction (representative 2229) := by
  apply obstruction_of_cachedAction 2229 [5, 2] 7 1
    (by decide) (by decide) (by decide) 242
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2230 : HasPrimeObstruction (representative 2230) := by
  apply obstruction_of_cachedAction 2230 [5] 7 1
    (by decide) (by decide) (by decide) 11
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2231 : HasPrimeObstruction (representative 2231) := by
  apply obstruction_of_cachedAction 2231 [5] 7 1
    (by decide) (by decide) (by decide) 58
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2232 : HasPrimeObstruction (representative 2232) := by
  apply obstruction_of_cachedAction 2232 [5] 7 1
    (by decide) (by decide) (by decide) 54
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2233 : HasPrimeObstruction (representative 2233) := by
  apply obstruction_of_cachedAction 2233 [5] 7 1
    (by decide) (by decide) (by decide) 43
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2234 : HasPrimeObstruction (representative 2234) := by
  apply obstruction_of_cachedAction 2234 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2235 : HasPrimeObstruction (representative 2235) := by
  apply obstruction_of_cachedAction 2235 [5] 7 1
    (by decide) (by decide) (by decide) 91
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2236 : HasPrimeObstruction (representative 2236) := by
  apply obstruction_of_cachedAction 2236 [5] 7 1
    (by decide) (by decide) (by decide) 16
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2237 : HasPrimeObstruction (representative 2237) := by
  apply obstruction_of_cachedAction 2237 [5, 4] 5 1
    (by decide) (by decide) (by decide) 26
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2238 : HasPrimeObstruction (representative 2238) := by
  apply obstruction_of_cachedAction 2238 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2239 : HasPrimeObstruction (representative 2239) := by
  apply obstruction_of_cachedAction 2239 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2240 : HasPrimeObstruction (representative 2240) := by
  apply obstruction_of_cachedAction 2240 [5, 3] 5 1
    (by decide) (by decide) (by decide) 2
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2241 : HasPrimeObstruction (representative 2241) := by
  apply obstruction_of_cachedAction 2241 [5] 7 1
    (by decide) (by decide) (by decide) 46
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2242 : HasPrimeObstruction (representative 2242) := by
  apply obstruction_of_cachedAction 2242 [5, 1] 5 1
    (by decide) (by decide) (by decide) 4
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2243 : HasPrimeObstruction (representative 2243) := by
  apply obstruction_of_cachedAction 2243 [5] 7 1
    (by decide) (by decide) (by decide) 29
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2244 : HasPrimeObstruction (representative 2244) := by
  apply obstruction_of_cachedAction 2244 [5, 3] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2245 : HasPrimeObstruction (representative 2245) := by
  apply obstruction_of_cachedAction 2245 [5] 7 1
    (by decide) (by decide) (by decide) 37
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2246 : HasPrimeObstruction (representative 2246) := by
  apply obstruction_of_cachedAction 2246 [5, 3] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2247 : HasPrimeObstruction (representative 2247) := by
  apply obstruction_of_cachedAction 2247 [5, 1] 7 1
    (by decide) (by decide) (by decide) 18
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2248 : HasPrimeObstruction (representative 2248) := by
  apply obstruction_of_cachedAction 2248 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2249 : HasPrimeObstruction (representative 2249) := by
  apply obstruction_of_cachedAction 2249 [5] 7 1
    (by decide) (by decide) (by decide) 41
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2250 : HasPrimeObstruction (representative 2250) := by
  apply obstruction_of_cachedAction 2250 [5] 7 1
    (by decide) (by decide) (by decide) 315
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2251 : HasPrimeObstruction (representative 2251) := by
  apply obstruction_of_cachedAction 2251 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2252 : HasPrimeObstruction (representative 2252) := by
  apply obstruction_of_cachedAction 2252 [5, 3] 7 1
    (by decide) (by decide) (by decide) 91
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2253 : HasPrimeObstruction (representative 2253) := by
  apply obstruction_of_cachedAction 2253 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2254 : HasPrimeObstruction (representative 2254) := by
  apply obstruction_of_cachedAction 2254 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2255 : HasPrimeObstruction (representative 2255) := by
  apply obstruction_of_cachedAction 2255 [5] 7 1
    (by decide) (by decide) (by decide) 14
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2256 : HasPrimeObstruction (representative 2256) := by
  apply obstruction_of_cachedAction 2256 [5] 7 1
    (by decide) (by decide) (by decide) 486
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2257 : HasPrimeObstruction (representative 2257) := by
  apply obstruction_of_cachedAction 2257 [5] 7 1
    (by decide) (by decide) (by decide) 78
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2258 : HasPrimeObstruction (representative 2258) := by
  apply obstruction_of_cachedAction 2258 [5] 7 1
    (by decide) (by decide) (by decide) 102
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2259 : HasPrimeObstruction (representative 2259) := by
  apply obstruction_of_cachedAction 2259 [5] 7 1
    (by decide) (by decide) (by decide) 34
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2260 : HasPrimeObstruction (representative 2260) := by
  apply obstruction_of_cachedAction 2260 [5] 7 1
    (by decide) (by decide) (by decide) 102
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2261 : HasPrimeObstruction (representative 2261) := by
  apply obstruction_of_cachedAction 2261 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2262 : HasPrimeObstruction (representative 2262) := by
  apply obstruction_of_cachedAction 2262 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2263 : HasPrimeObstruction (representative 2263) := by
  apply obstruction_of_cachedAction 2263 [5, 1] 7 1
    (by decide) (by decide) (by decide) 11
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2264 : HasPrimeObstruction (representative 2264) := by
  apply obstruction_of_cachedAction 2264 [5] 7 1
    (by decide) (by decide) (by decide) 10
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2265 : HasPrimeObstruction (representative 2265) := by
  apply obstruction_of_cachedAction 2265 [5] 7 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2266 : HasPrimeObstruction (representative 2266) := by
  apply obstruction_of_cachedAction 2266 [5] 7 1
    (by decide) (by decide) (by decide) 114
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2267 : HasPrimeObstruction (representative 2267) := by
  apply obstruction_of_cachedAction 2267 [5] 7 1
    (by decide) (by decide) (by decide) 2
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2268 : HasPrimeObstruction (representative 2268) := by
  apply obstruction_of_cachedAction 2268 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2269 : HasPrimeObstruction (representative 2269) := by
  apply obstruction_of_cachedAction 2269 [5, 2] 7 1
    (by decide) (by decide) (by decide) 19
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2270 : HasPrimeObstruction (representative 2270) := by
  apply obstruction_of_cachedAction 2270 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2271 : HasPrimeObstruction (representative 2271) := by
  apply obstruction_of_cachedAction 2271 [5] 5 1
    (by decide) (by decide) (by decide) 44
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2272 : HasPrimeObstruction (representative 2272) := by
  apply obstruction_of_cachedAction 2272 [5] 5 1
    (by decide) (by decide) (by decide) 23
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2273 : HasPrimeObstruction (representative 2273) := by
  apply obstruction_of_cachedAction 2273 [5] 7 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2274 : HasPrimeObstruction (representative 2274) := by
  apply obstruction_of_cachedAction 2274 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2275 : HasPrimeObstruction (representative 2275) := by
  apply obstruction_of_cachedAction 2275 [5] 7 1
    (by decide) (by decide) (by decide) 356
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2276 : HasPrimeObstruction (representative 2276) := by
  apply obstruction_of_cachedAction 2276 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2277 : HasPrimeObstruction (representative 2277) := by
  apply obstruction_of_cachedAction 2277 [5, 1] 5 1
    (by decide) (by decide) (by decide) 12
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2278 : HasPrimeObstruction (representative 2278) := by
  apply obstruction_of_cachedAction 2278 [5] 5 1
    (by decide) (by decide) (by decide) 3
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2279 : HasPrimeObstruction (representative 2279) := by
  apply obstruction_of_cachedAction 2279 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2280 : HasPrimeObstruction (representative 2280) := by
  apply obstruction_of_cachedAction 2280 [5, 2] 5 1
    (by decide) (by decide) (by decide) 25
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2281 : HasPrimeObstruction (representative 2281) := by
  apply obstruction_of_cachedAction 2281 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2282 : HasPrimeObstruction (representative 2282) := by
  apply obstruction_of_cachedAction 2282 [5] 5 1
    (by decide) (by decide) (by decide) 52
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2283 : HasPrimeObstruction (representative 2283) := by
  apply obstruction_of_cachedAction 2283 [5] 5 1
    (by decide) (by decide) (by decide) 30
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2284 : HasPrimeObstruction (representative 2284) := by
  apply obstruction_of_cachedAction 2284 [5] 5 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2285 : HasPrimeObstruction (representative 2285) := by
  apply obstruction_of_cachedAction 2285 [5, 2] 5 1
    (by decide) (by decide) (by decide) 45
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2286 : HasPrimeObstruction (representative 2286) := by
  apply obstruction_of_cachedAction 2286 [5, 1] 7 1
    (by decide) (by decide) (by decide) 235
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2287 : HasPrimeObstruction (representative 2287) := by
  apply obstruction_of_cachedAction 2287 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2288 : HasPrimeObstruction (representative 2288) := by
  apply obstruction_of_cachedAction 2288 [5, 4] 5 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2289 : HasPrimeObstruction (representative 2289) := by
  apply obstruction_of_cachedAction 2289 [5, 2] 5 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2290 : HasPrimeObstruction (representative 2290) := by
  apply obstruction_of_cachedAction 2290 [5] 7 1
    (by decide) (by decide) (by decide) 38
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2291 : HasPrimeObstruction (representative 2291) := by
  apply obstruction_of_cachedAction 2291 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2292 : HasPrimeObstruction (representative 2292) := by
  apply obstruction_of_cachedAction 2292 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2293 : HasPrimeObstruction (representative 2293) := by
  apply obstruction_of_cachedAction 2293 [5] 7 1
    (by decide) (by decide) (by decide) 109
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2294 : HasPrimeObstruction (representative 2294) := by
  apply obstruction_of_cachedAction 2294 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2295 : HasPrimeObstruction (representative 2295) := by
  apply obstruction_of_cachedAction 2295 [5, 1] 5 1
    (by decide) (by decide) (by decide) 11
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2296 : HasPrimeObstruction (representative 2296) := by
  apply obstruction_of_cachedAction 2296 [5] 7 1
    (by decide) (by decide) (by decide) 19
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2297 : HasPrimeObstruction (representative 2297) := by
  apply obstruction_of_cachedAction 2297 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2298 : HasPrimeObstruction (representative 2298) := by
  apply obstruction_of_cachedAction 2298 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2299 : HasPrimeObstruction (representative 2299) := by
  apply obstruction_of_cachedAction 2299 [5, 4] 7 1
    (by decide) (by decide) (by decide) 30
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2300 : HasPrimeObstruction (representative 2300) := by
  apply obstruction_of_cachedAction 2300 [5] 7 1
    (by decide) (by decide) (by decide) 13
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2301 : HasPrimeObstruction (representative 2301) := by
  apply obstruction_of_cachedAction 2301 [5, 1] 5 1
    (by decide) (by decide) (by decide) 95
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2302 : HasPrimeObstruction (representative 2302) := by
  apply obstruction_of_cachedAction 2302 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2303 : HasPrimeObstruction (representative 2303) := by
  apply obstruction_of_cachedAction 2303 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

/-- Every nonlocal representative in this interval has a forbidden prime order. -/
public theorem obstruction_block08 (j : Fin 256)
    (h : localBranch ⟨2048 + j.val, by omega⟩ = none) :
    HasPrimeObstruction (representative ⟨2048 + j.val, by omega⟩) := by
  fin_cases j
  · exact obstruction_2048
  · exact obstruction_2049
  · exact obstruction_2050
  · exact obstruction_2051
  · exact obstruction_2052
  · exact obstruction_2053
  · exact obstruction_2054
  · exact obstruction_2055
  · exact obstruction_2056
  · exact obstruction_2057
  · exact obstruction_2058
  · exact obstruction_2059
  · exact obstruction_2060
  · exact obstruction_2061
  · exact obstruction_2062
  · exact obstruction_2063
  · exact obstruction_2064
  · exact obstruction_2065
  · exact obstruction_2066
  · exact obstruction_2067
  · exact obstruction_2068
  · exact obstruction_2069
  · exact obstruction_2070
  · exact obstruction_2071
  · exact obstruction_2072
  · exact obstruction_2073
  · exact obstruction_2074
  · exact obstruction_2075
  · exact obstruction_2076
  · exact obstruction_2077
  · exact obstruction_2078
  · exact obstruction_2079
  · exact obstruction_2080
  · exact obstruction_2081
  · exact obstruction_2082
  · exact obstruction_2083
  · exact obstruction_2084
  · exact obstruction_2085
  · exact obstruction_2086
  · exact obstruction_2087
  · exact obstruction_2088
  · exact obstruction_2089
  · exact obstruction_2090
  · exact obstruction_2091
  · exact obstruction_2092
  · exact obstruction_2093
  · exact obstruction_2094
  · exact obstruction_2095
  · exact obstruction_2096
  · exact obstruction_2097
  · exact obstruction_2098
  · exact obstruction_2099
  · exact obstruction_2100
  · exact obstruction_2101
  · exact obstruction_2102
  · exact obstruction_2103
  · exact obstruction_2104
  · exact obstruction_2105
  · exact obstruction_2106
  · exact obstruction_2107
  · exact obstruction_2108
  · exact obstruction_2109
  · exact obstruction_2110
  · exact obstruction_2111
  · exact obstruction_2112
  · exact obstruction_2113
  · exact obstruction_2114
  · exact obstruction_2115
  · exact obstruction_2116
  · exact obstruction_2117
  · exact obstruction_2118
  · exact obstruction_2119
  · exact obstruction_2120
  · exact obstruction_2121
  · exact obstruction_2122
  · exact obstruction_2123
  · exact obstruction_2124
  · exact obstruction_2125
  · exact obstruction_2126
  · exact obstruction_2127
  · exact obstruction_2128
  · exact obstruction_2129
  · exact obstruction_2130
  · exact obstruction_2131
  · exact obstruction_2132
  · exact obstruction_2133
  · exact obstruction_2134
  · exact obstruction_2135
  · exact obstruction_2136
  · exact obstruction_2137
  · exact obstruction_2138
  · exact obstruction_2139
  · exact obstruction_2140
  · exact obstruction_2141
  · exact obstruction_2142
  · exact obstruction_2143
  · exact obstruction_2144
  · exact obstruction_2145
  · exact obstruction_2146
  · exact obstruction_2147
  · exact obstruction_2148
  · exact obstruction_2149
  · exact obstruction_2150
  · exact obstruction_2151
  · exact obstruction_2152
  · exact obstruction_2153
  · exact obstruction_2154
  · exact obstruction_2155
  · exact obstruction_2156
  · exact obstruction_2157
  · exact obstruction_2158
  · exact obstruction_2159
  · exact obstruction_2160
  · exact obstruction_2161
  · exact obstruction_2162
  · exact obstruction_2163
  · exact obstruction_2164
  · exact obstruction_2165
  · exact obstruction_2166
  · exact obstruction_2167
  · exact obstruction_2168
  · exact obstruction_2169
  · exact obstruction_2170
  · exact obstruction_2171
  · exact obstruction_2172
  · exact obstruction_2173
  · exact obstruction_2174
  · exact obstruction_2175
  · exact obstruction_2176
  · exact obstruction_2177
  · exact obstruction_2178
  · exact obstruction_2179
  · exact obstruction_2180
  · exact obstruction_2181
  · exact obstruction_2182
  · exact obstruction_2183
  · exact obstruction_2184
  · exact obstruction_2185
  · exact obstruction_2186
  · exact obstruction_2187
  · exact obstruction_2188
  · exact obstruction_2189
  · exact obstruction_2190
  · exact obstruction_2191
  · exact obstruction_2192
  · exact obstruction_2193
  · exact obstruction_2194
  · exact obstruction_2195
  · exact obstruction_2196
  · exact obstruction_2197
  · exact obstruction_2198
  · exact obstruction_2199
  · exact obstruction_2200
  · exact obstruction_2201
  · exact obstruction_2202
  · exact obstruction_2203
  · exact obstruction_2204
  · exact obstruction_2205
  · exact obstruction_2206
  · exact obstruction_2207
  · exact obstruction_2208
  · exact obstruction_2209
  · exact obstruction_2210
  · exact obstruction_2211
  · exact obstruction_2212
  · exact obstruction_2213
  · exact obstruction_2214
  · exact obstruction_2215
  · exact obstruction_2216
  · exact obstruction_2217
  · exact obstruction_2218
  · exact obstruction_2219
  · exact obstruction_2220
  · exact obstruction_2221
  · exact obstruction_2222
  · exact obstruction_2223
  · exact obstruction_2224
  · exact obstruction_2225
  · exact obstruction_2226
  · exact obstruction_2227
  · exact obstruction_2228
  · exact obstruction_2229
  · exact obstruction_2230
  · exact obstruction_2231
  · exact obstruction_2232
  · exact obstruction_2233
  · exact obstruction_2234
  · exact obstruction_2235
  · exact obstruction_2236
  · exact obstruction_2237
  · exact obstruction_2238
  · exact obstruction_2239
  · exact obstruction_2240
  · exact obstruction_2241
  · exact obstruction_2242
  · exact obstruction_2243
  · exact obstruction_2244
  · exact obstruction_2245
  · exact obstruction_2246
  · exact obstruction_2247
  · exact obstruction_2248
  · exact obstruction_2249
  · exact obstruction_2250
  · exact obstruction_2251
  · exact obstruction_2252
  · exact obstruction_2253
  · exact obstruction_2254
  · exact obstruction_2255
  · exact obstruction_2256
  · exact obstruction_2257
  · exact obstruction_2258
  · exact obstruction_2259
  · exact obstruction_2260
  · exact obstruction_2261
  · exact obstruction_2262
  · exact obstruction_2263
  · exact obstruction_2264
  · exact obstruction_2265
  · exact obstruction_2266
  · exact obstruction_2267
  · exact obstruction_2268
  · exact obstruction_2269
  · exact obstruction_2270
  · exact obstruction_2271
  · exact obstruction_2272
  · exact obstruction_2273
  · exact obstruction_2274
  · exact obstruction_2275
  · exact obstruction_2276
  · exact obstruction_2277
  · exact obstruction_2278
  · exact obstruction_2279
  · exact obstruction_2280
  · exact obstruction_2281
  · exact obstruction_2282
  · exact obstruction_2283
  · exact obstruction_2284
  · exact obstruction_2285
  · exact obstruction_2286
  · exact obstruction_2287
  · exact obstruction_2288
  · exact obstruction_2289
  · exact obstruction_2290
  · exact obstruction_2291
  · exact obstruction_2292
  · exact obstruction_2293
  · exact obstruction_2294
  · exact obstruction_2295
  · exact obstruction_2296
  · exact obstruction_2297
  · exact obstruction_2298
  · exact obstruction_2299
  · exact obstruction_2300
  · exact obstruction_2301
  · exact obstruction_2302
  · exact obstruction_2303

end Held.LocalPairs.PairCoverage.SylowOvergroups.RepresentativeVerification
