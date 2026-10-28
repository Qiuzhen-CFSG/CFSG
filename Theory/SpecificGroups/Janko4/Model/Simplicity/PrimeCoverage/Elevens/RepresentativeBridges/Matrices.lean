module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Elevens.RepresentativeBridges.Products00
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Elevens.RepresentativeBridges.Products01
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Elevens.RepresentativeBridges.Products02
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Elevens.RepresentativeBridges.Products03
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Elevens.RepresentativeBridges.Products04
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Elevens.RepresentativeBridges.Products05
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Elevens.RepresentativeBridges.Products06
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Elevens.RepresentativeBridges.Products07
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Elevens.RepresentativeBridges.Products08
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Elevens.RepresentativeBridges.Products09
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Elevens.RepresentativeBridges.Witnesses

/-!
# Matrix certificates for the conjugating words

Certified packed products evaluate every multiplication, inverse, and power
in the explicit straight-line witnesses. The faithful representation then
proves the two group identities. No order or conjugacy classification is used.
-/

public section
namespace Janko4.Simplicity.Elevens.BridgeCertificate

theorem power007_2 : decodeRows v007 ^ 2 = decodeRows v008 := by
  calc
    _ = decodeRows v007 ^ 1 * decodeRows v007 ^ 1 := by rw [← pow_add]
    _ = _ := by simp only [pow_one, product005]

theorem power007_4 : decodeRows v007 ^ 4 = decodeRows v009 := by
  calc
    _ = decodeRows v007 ^ 2 * decodeRows v007 ^ 2 := by rw [← pow_add]
    _ = _ := by simp only [power007_2, product006]

theorem power007_8 : decodeRows v007 ^ 8 = decodeRows v010 := by
  calc
    _ = decodeRows v007 ^ 4 * decodeRows v007 ^ 4 := by rw [← pow_add]
    _ = _ := by simp only [power007_4, product007]

theorem power004_2 : decodeRows v004 ^ 2 = decodeRows v012 := by
  calc
    _ = decodeRows v004 ^ 1 * decodeRows v004 ^ 1 := by rw [← pow_add]
    _ = _ := by simp only [pow_one, product009]

theorem power004_4 : decodeRows v004 ^ 4 = decodeRows v013 := by
  calc
    _ = decodeRows v004 ^ 2 * decodeRows v004 ^ 2 := by rw [← pow_add]
    _ = _ := by simp only [power004_2, product010]

theorem power016_2 : decodeRows v016 ^ 2 = decodeRows v017 := by
  calc
    _ = decodeRows v016 ^ 1 * decodeRows v016 ^ 1 := by rw [← pow_add]
    _ = _ := by simp only [pow_one, product014]

theorem power016_3 : decodeRows v016 ^ 3 = decodeRows v018 := by
  calc
    _ = decodeRows v016 ^ 1 * decodeRows v016 ^ 2 := by rw [← pow_add]
    _ = _ := by simp only [pow_one, power016_2, product015]

theorem power016_6 : decodeRows v016 ^ 6 = decodeRows v019 := by
  calc
    _ = decodeRows v016 ^ 3 * decodeRows v016 ^ 3 := by rw [← pow_add]
    _ = _ := by simp only [power016_3, product016]

theorem power020_2 : decodeRows v020 ^ 2 = decodeRows v021 := by
  calc
    _ = decodeRows v020 ^ 1 * decodeRows v020 ^ 1 := by rw [← pow_add]
    _ = _ := by simp only [pow_one, product018]

theorem power020_3 : decodeRows v020 ^ 3 = decodeRows v022 := by
  calc
    _ = decodeRows v020 ^ 1 * decodeRows v020 ^ 2 := by rw [← pow_add]
    _ = _ := by simp only [pow_one, power020_2, product019]

theorem power024_2 : decodeRows v024 ^ 2 = decodeRows v025 := by
  calc
    _ = decodeRows v024 ^ 1 * decodeRows v024 ^ 1 := by rw [← pow_add]
    _ = _ := by simp only [pow_one, product022]

theorem power024_4 : decodeRows v024 ^ 4 = decodeRows v026 := by
  calc
    _ = decodeRows v024 ^ 2 * decodeRows v024 ^ 2 := by rw [← pow_add]
    _ = _ := by simp only [power024_2, product023]

theorem power024_8 : decodeRows v024 ^ 8 = decodeRows v027 := by
  calc
    _ = decodeRows v024 ^ 4 * decodeRows v024 ^ 4 := by rw [← pow_add]
    _ = _ := by simp only [power024_4, product024]

theorem power024_3 : decodeRows v024 ^ 3 = decodeRows v028 := by
  calc
    _ = decodeRows v024 ^ 1 * decodeRows v024 ^ 2 := by rw [← pow_add]
    _ = _ := by simp only [pow_one, power024_2, product025]

theorem power024_5 : decodeRows v024 ^ 5 = decodeRows v029 := by
  calc
    _ = decodeRows v024 ^ 2 * decodeRows v024 ^ 3 := by rw [← pow_add]
    _ = _ := by simp only [power024_2, power024_3, product026]

theorem power024_10 : decodeRows v024 ^ 10 = decodeRows v030 := by
  calc
    _ = decodeRows v024 ^ 5 * decodeRows v024 ^ 5 := by rw [← pow_add]
    _ = _ := by simp only [power024_5, product027]

theorem power024_20 : decodeRows v024 ^ 20 = decodeRows v031 := by
  calc
    _ = decodeRows v024 ^ 10 * decodeRows v024 ^ 10 := by rw [← pow_add]
    _ = _ := by simp only [power024_10, product028]

theorem power035_2 : decodeRows v035 ^ 2 = decodeRows v036 := by
  calc
    _ = decodeRows v035 ^ 1 * decodeRows v035 ^ 1 := by rw [← pow_add]
    _ = _ := by simp only [pow_one, product033]

theorem power035_3 : decodeRows v035 ^ 3 = decodeRows v037 := by
  calc
    _ = decodeRows v035 ^ 1 * decodeRows v035 ^ 2 := by rw [← pow_add]
    _ = _ := by simp only [pow_one, power035_2, product034]

theorem power044_2 : decodeRows v044 ^ 2 = decodeRows v045 := by
  calc
    _ = decodeRows v044 ^ 1 * decodeRows v044 ^ 1 := by rw [← pow_add]
    _ = _ := by simp only [pow_one, product042]

theorem power044_3 : decodeRows v044 ^ 3 = decodeRows v046 := by
  calc
    _ = decodeRows v044 ^ 1 * decodeRows v044 ^ 2 := by rw [← pow_add]
    _ = _ := by simp only [pow_one, power044_2, product043]

theorem power044_4 : decodeRows v044 ^ 4 = decodeRows v047 := by
  calc
    _ = decodeRows v044 ^ 2 * decodeRows v044 ^ 2 := by rw [← pow_add]
    _ = _ := by simp only [power044_2, product044]

theorem power044_7 : decodeRows v044 ^ 7 = decodeRows v048 := by
  calc
    _ = decodeRows v044 ^ 3 * decodeRows v044 ^ 4 := by rw [← pow_add]
    _ = _ := by simp only [power044_3, power044_4, product045]

theorem power051_2 : decodeRows v051 ^ 2 = decodeRows v052 := by
  calc
    _ = decodeRows v051 ^ 1 * decodeRows v051 ^ 1 := by rw [← pow_add]
    _ = _ := by simp only [pow_one, product049]

theorem power051_3 : decodeRows v051 ^ 3 = decodeRows v053 := by
  calc
    _ = decodeRows v051 ^ 1 * decodeRows v051 ^ 2 := by rw [← pow_add]
    _ = _ := by simp only [pow_one, power051_2, product050]

theorem power051_4 : decodeRows v051 ^ 4 = decodeRows v054 := by
  calc
    _ = decodeRows v051 ^ 2 * decodeRows v051 ^ 2 := by rw [← pow_add]
    _ = _ := by simp only [power051_2, product051]

theorem power051_7 : decodeRows v051 ^ 7 = decodeRows v055 := by
  calc
    _ = decodeRows v051 ^ 3 * decodeRows v051 ^ 4 := by rw [← pow_add]
    _ = _ := by simp only [power051_3, power051_4, product052]

theorem power051_8 : decodeRows v051 ^ 8 = decodeRows v056 := by
  calc
    _ = decodeRows v051 ^ 4 * decodeRows v051 ^ 4 := by rw [← pow_add]
    _ = _ := by simp only [power051_4, product053]

theorem power051_15 : decodeRows v051 ^ 15 = decodeRows v057 := by
  calc
    _ = decodeRows v051 ^ 7 * decodeRows v051 ^ 8 := by rw [← pow_add]
    _ = _ := by simp only [power051_7, power051_8, product054]

theorem power058_2 : decodeRows v058 ^ 2 = decodeRows v059 := by
  calc
    _ = decodeRows v058 ^ 1 * decodeRows v058 ^ 1 := by rw [← pow_add]
    _ = _ := by simp only [pow_one, product056]

theorem power074_2 : decodeRows v074 ^ 2 = decodeRows v075 := by
  calc
    _ = decodeRows v074 ^ 1 * decodeRows v074 ^ 1 := by rw [← pow_add]
    _ = _ := by simp only [pow_one, product072]

theorem power074_3 : decodeRows v074 ^ 3 = decodeRows v076 := by
  calc
    _ = decodeRows v074 ^ 1 * decodeRows v074 ^ 2 := by rw [← pow_add]
    _ = _ := by simp only [pow_one, power074_2, product073]

theorem power074_6 : decodeRows v074 ^ 6 = decodeRows v077 := by
  calc
    _ = decodeRows v074 ^ 3 * decodeRows v074 ^ 3 := by rw [← pow_add]
    _ = _ := by simp only [power074_3, product074]

theorem power074_4 : decodeRows v074 ^ 4 = decodeRows v078 := by
  calc
    _ = decodeRows v074 ^ 2 * decodeRows v074 ^ 2 := by rw [← pow_add]
    _ = _ := by simp only [power074_2, product075]

theorem power074_8 : decodeRows v074 ^ 8 = decodeRows v079 := by
  calc
    _ = decodeRows v074 ^ 4 * decodeRows v074 ^ 4 := by rw [← pow_add]
    _ = _ := by simp only [power074_4, product076]

theorem power074_16 : decodeRows v074 ^ 16 = decodeRows v080 := by
  calc
    _ = decodeRows v074 ^ 8 * decodeRows v074 ^ 8 := by rw [← pow_add]
    _ = _ := by simp only [power074_8, product077]

theorem power074_5 : decodeRows v074 ^ 5 = decodeRows v081 := by
  calc
    _ = decodeRows v074 ^ 2 * decodeRows v074 ^ 3 := by rw [← pow_add]
    _ = _ := by simp only [power074_2, power074_3, product078]

theorem power074_9 : decodeRows v074 ^ 9 = decodeRows v082 := by
  calc
    _ = decodeRows v074 ^ 4 * decodeRows v074 ^ 5 := by rw [← pow_add]
    _ = _ := by simp only [power074_4, power074_5, product079]

theorem power074_17 : decodeRows v074 ^ 17 = decodeRows v083 := by
  calc
    _ = decodeRows v074 ^ 8 * decodeRows v074 ^ 9 := by rw [← pow_add]
    _ = _ := by simp only [power074_8, power074_9, product080]

theorem power074_33 : decodeRows v074 ^ 33 = decodeRows v084 := by
  calc
    _ = decodeRows v074 ^ 16 * decodeRows v074 ^ 17 := by rw [← pow_add]
    _ = _ := by simp only [power074_16, power074_17, product081]

theorem power096_2 : decodeRows v096 ^ 2 = decodeRows v097 := by
  calc
    _ = decodeRows v096 ^ 1 * decodeRows v096 ^ 1 := by rw [← pow_add]
    _ = _ := by simp only [pow_one, product097]

theorem power096_3 : decodeRows v096 ^ 3 = decodeRows v098 := by
  calc
    _ = decodeRows v096 ^ 1 * decodeRows v096 ^ 2 := by rw [← pow_add]
    _ = _ := by simp only [pow_one, power096_2, product098]

theorem power096_6 : decodeRows v096 ^ 6 = decodeRows v099 := by
  calc
    _ = decodeRows v096 ^ 3 * decodeRows v096 ^ 3 := by rw [← pow_add]
    _ = _ := by simp only [power096_3, product099]

theorem power067_2 : decodeRows v067 ^ 2 = decodeRows v123 := by
  calc
    _ = decodeRows v067 ^ 1 * decodeRows v067 ^ 1 := by rw [← pow_add]
    _ = _ := by simp only [pow_one, product127]

theorem power067_3 : decodeRows v067 ^ 3 = decodeRows v124 := by
  calc
    _ = decodeRows v067 ^ 1 * decodeRows v067 ^ 2 := by rw [← pow_add]
    _ = _ := by simp only [pow_one, power067_2, product128]

theorem power067_4 : decodeRows v067 ^ 4 = decodeRows v125 := by
  calc
    _ = decodeRows v067 ^ 2 * decodeRows v067 ^ 2 := by rw [← pow_add]
    _ = _ := by simp only [power067_2, product129]

theorem power067_7 : decodeRows v067 ^ 7 = decodeRows v126 := by
  calc
    _ = decodeRows v067 ^ 3 * decodeRows v067 ^ 4 := by rw [← pow_add]
    _ = _ := by simp only [power067_3, power067_4, product130]

theorem power145_2 : decodeRows v145 ^ 2 = decodeRows v146 := by
  calc
    _ = decodeRows v145 ^ 1 * decodeRows v145 ^ 1 := by rw [← pow_add]
    _ = _ := by simp only [pow_one, product151]

theorem power145_3 : decodeRows v145 ^ 3 = decodeRows v147 := by
  calc
    _ = decodeRows v145 ^ 1 * decodeRows v145 ^ 2 := by rw [← pow_add]
    _ = _ := by simp only [pow_one, power145_2, product152]

theorem power145_5 : decodeRows v145 ^ 5 = decodeRows v148 := by
  calc
    _ = decodeRows v145 ^ 2 * decodeRows v145 ^ 3 := by rw [← pow_add]
    _ = _ := by simp only [power145_2, power145_3, product153]

theorem power145_6 : decodeRows v145 ^ 6 = decodeRows v149 := by
  calc
    _ = decodeRows v145 ^ 3 * decodeRows v145 ^ 3 := by rw [← pow_add]
    _ = _ := by simp only [power145_3, product154]

theorem power145_11 : decodeRows v145 ^ 11 = decodeRows v150 := by
  calc
    _ = decodeRows v145 ^ 5 * decodeRows v145 ^ 6 := by rw [← pow_add]
    _ = _ := by simp only [power145_5, power145_6, product155]

theorem power163_2 : decodeRows v163 ^ 2 = decodeRows v164 := by
  calc
    _ = decodeRows v163 ^ 1 * decodeRows v163 ^ 1 := by rw [← pow_add]
    _ = _ := by simp only [pow_one, product172]

theorem power163_3 : decodeRows v163 ^ 3 = decodeRows v165 := by
  calc
    _ = decodeRows v163 ^ 1 * decodeRows v163 ^ 2 := by rw [← pow_add]
    _ = _ := by simp only [pow_one, power163_2, product173]

theorem power163_5 : decodeRows v163 ^ 5 = decodeRows v166 := by
  calc
    _ = decodeRows v163 ^ 2 * decodeRows v163 ^ 3 := by rw [← pow_add]
    _ = _ := by simp only [power163_2, power163_3, product174]

theorem power172_2 : decodeRows v172 ^ 2 = decodeRows v173 := by
  calc
    _ = decodeRows v172 ^ 1 * decodeRows v172 ^ 1 := by rw [← pow_add]
    _ = _ := by simp only [pow_one, product181]

theorem power172_4 : decodeRows v172 ^ 4 = decodeRows v174 := by
  calc
    _ = decodeRows v172 ^ 2 * decodeRows v172 ^ 2 := by rw [← pow_add]
    _ = _ := by simp only [power172_2, product182]

theorem power172_3 : decodeRows v172 ^ 3 = decodeRows v175 := by
  calc
    _ = decodeRows v172 ^ 1 * decodeRows v172 ^ 2 := by rw [← pow_add]
    _ = _ := by simp only [pow_one, power172_2, product183]

theorem power172_5 : decodeRows v172 ^ 5 = decodeRows v176 := by
  calc
    _ = decodeRows v172 ^ 2 * decodeRows v172 ^ 3 := by rw [← pow_add]
    _ = _ := by simp only [power172_2, power172_3, product184]

theorem power172_9 : decodeRows v172 ^ 9 = decodeRows v177 := by
  calc
    _ = decodeRows v172 ^ 4 * decodeRows v172 ^ 5 := by rw [← pow_add]
    _ = _ := by simp only [power172_4, power172_5, product185]

theorem power172_10 : decodeRows v172 ^ 10 = decodeRows v178 := by
  calc
    _ = decodeRows v172 ^ 5 * decodeRows v172 ^ 5 := by rw [← pow_add]
    _ = _ := by simp only [power172_5, product186]

theorem power172_19 : decodeRows v172 ^ 19 = decodeRows v179 := by
  calc
    _ = decodeRows v172 ^ 9 * decodeRows v172 ^ 10 := by rw [← pow_add]
    _ = _ := by simp only [power172_9, power172_10, product187]

theorem power196_2 : decodeRows v196 ^ 2 = decodeRows v197 := by
  calc
    _ = decodeRows v196 ^ 1 * decodeRows v196 ^ 1 := by rw [← pow_add]
    _ = _ := by simp only [pow_one, product211]

theorem power196_3 : decodeRows v196 ^ 3 = decodeRows v198 := by
  calc
    _ = decodeRows v196 ^ 1 * decodeRows v196 ^ 2 := by rw [← pow_add]
    _ = _ := by simp only [pow_one, power196_2, product212]

theorem power196_6 : decodeRows v196 ^ 6 = decodeRows v199 := by
  calc
    _ = decodeRows v196 ^ 3 * decodeRows v196 ^ 3 := by rw [← pow_add]
    _ = _ := by simp only [power196_3, product213]

theorem power196_12 : decodeRows v196 ^ 12 = decodeRows v200 := by
  calc
    _ = decodeRows v196 ^ 6 * decodeRows v196 ^ 6 := by rw [← pow_add]
    _ = _ := by simp only [power196_6, product214]

theorem power217_2 : decodeRows v217 ^ 2 = decodeRows v218 := by
  calc
    _ = decodeRows v217 ^ 1 * decodeRows v217 ^ 1 := by rw [← pow_add]
    _ = _ := by simp only [pow_one, product236]

theorem power217_3 : decodeRows v217 ^ 3 = decodeRows v219 := by
  calc
    _ = decodeRows v217 ^ 1 * decodeRows v217 ^ 2 := by rw [← pow_add]
    _ = _ := by simp only [pow_one, power217_2, product237]

theorem power217_5 : decodeRows v217 ^ 5 = decodeRows v220 := by
  calc
    _ = decodeRows v217 ^ 2 * decodeRows v217 ^ 3 := by rw [← pow_add]
    _ = _ := by simp only [power217_2, power217_3, product238]

theorem power217_10 : decodeRows v217 ^ 10 = decodeRows v221 := by
  calc
    _ = decodeRows v217 ^ 5 * decodeRows v217 ^ 5 := by rw [← pow_add]
    _ = _ := by simp only [power217_5, product239]

theorem power217_20 : decodeRows v217 ^ 20 = decodeRows v222 := by
  calc
    _ = decodeRows v217 ^ 10 * decodeRows v217 ^ 10 := by rw [← pow_add]
    _ = _ := by simp only [power217_10, product240]

theorem power234_2 : decodeRows v234 ^ 2 = decodeRows v235 := by
  calc
    _ = decodeRows v234 ^ 1 * decodeRows v234 ^ 1 := by rw [← pow_add]
    _ = _ := by simp only [pow_one, product256]

theorem power234_4 : decodeRows v234 ^ 4 = decodeRows v236 := by
  calc
    _ = decodeRows v234 ^ 2 * decodeRows v234 ^ 2 := by rw [← pow_add]
    _ = _ := by simp only [power234_2, product257]

theorem power234_8 : decodeRows v234 ^ 8 = decodeRows v237 := by
  calc
    _ = decodeRows v234 ^ 4 * decodeRows v234 ^ 4 := by rw [← pow_add]
    _ = _ := by simp only [power234_4, product258]

theorem power234_16 : decodeRows v234 ^ 16 = decodeRows v238 := by
  calc
    _ = decodeRows v234 ^ 8 * decodeRows v234 ^ 8 := by rw [← pow_add]
    _ = _ := by simp only [power234_8, product259]

theorem power252_2 : decodeRows v252 ^ 2 = decodeRows v253 := by
  calc
    _ = decodeRows v252 ^ 1 * decodeRows v252 ^ 1 := by rw [← pow_add]
    _ = _ := by simp only [pow_one, product277]

theorem power252_3 : decodeRows v252 ^ 3 = decodeRows v254 := by
  calc
    _ = decodeRows v252 ^ 1 * decodeRows v252 ^ 2 := by rw [← pow_add]
    _ = _ := by simp only [pow_one, power252_2, product278]

theorem power252_5 : decodeRows v252 ^ 5 = decodeRows v255 := by
  calc
    _ = decodeRows v252 ^ 2 * decodeRows v252 ^ 3 := by rw [← pow_add]
    _ = _ := by simp only [power252_2, power252_3, product279]

theorem power252_10 : decodeRows v252 ^ 10 = decodeRows v256 := by
  calc
    _ = decodeRows v252 ^ 5 * decodeRows v252 ^ 5 := by rw [← pow_add]
    _ = _ := by simp only [power252_5, product280]

theorem power252_20 : decodeRows v252 ^ 20 = decodeRows v257 := by
  calc
    _ = decodeRows v252 ^ 10 * decodeRows v252 ^ 10 := by rw [← pow_add]
    _ = _ := by simp only [power252_10, product281]

theorem power274_2 : decodeRows v274 ^ 2 = decodeRows v275 := by
  calc
    _ = decodeRows v274 ^ 1 * decodeRows v274 ^ 1 := by rw [← pow_add]
    _ = _ := by simp only [pow_one, product303]

theorem power274_3 : decodeRows v274 ^ 3 = decodeRows v276 := by
  calc
    _ = decodeRows v274 ^ 1 * decodeRows v274 ^ 2 := by rw [← pow_add]
    _ = _ := by simp only [pow_one, power274_2, product304]

theorem power274_6 : decodeRows v274 ^ 6 = decodeRows v277 := by
  calc
    _ = decodeRows v274 ^ 3 * decodeRows v274 ^ 3 := by rw [← pow_add]
    _ = _ := by simp only [power274_3, product305]

theorem power274_12 : decodeRows v274 ^ 12 = decodeRows v278 := by
  calc
    _ = decodeRows v274 ^ 6 * decodeRows v274 ^ 6 := by rw [← pow_add]
    _ = _ := by simp only [power274_6, product306]

variable (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)

theorem matrix_w000 : toMatrix (w000 (a hA) (b hB)) = decodeRows v001 := by
  exact decode_a.symm

theorem matrix_w001 : toMatrix (w001 (a hA) (b hB)) = decodeRows v002 := by
  exact decode_b.symm

theorem matrix_w002 : toMatrix (w002 (a hA) (b hB)) = decodeRows v003 := by
  exact mul_certificate _ _ _ _ _ (matrix_w000 hA hB) (matrix_w001 hA hB) product000

theorem matrix_w003 : toMatrix (w003 (a hA) (b hB)) = decodeRows v004 := by
  exact mul_certificate _ _ _ _ _ (matrix_w002 hA hB) (matrix_w001 hA hB) product001

theorem matrix_w004 : toMatrix (w004 (a hA) (b hB)) = decodeRows v005 := by
  exact mul_certificate _ _ _ _ _ (matrix_w002 hA hB) (matrix_w003 hA hB) product002

theorem matrix_w005 : toMatrix (w005 (a hA) (b hB)) = decodeRows v006 := by
  exact mul_certificate _ _ _ _ _ (matrix_w002 hA hB) (matrix_w004 hA hB) product003

theorem matrix_w006 : toMatrix (w006 (a hA) (b hB)) = decodeRows v007 := by
  exact mul_certificate _ _ _ _ _ (matrix_w005 hA hB) (matrix_w003 hA hB) product004

theorem matrix_w007 : toMatrix (w007 (a hA) (b hB)) = decodeRows v010 := by
  rw [w007, map_pow, matrix_w006 hA hB, power007_8]

theorem matrix_w008 : toMatrix (w008 (a hA) (b hB)) = decodeRows v011 := by
  exact inv_certificate _ _ _ (matrix_w007 hA hB) (product008.trans decode_identity)

theorem matrix_w009 : toMatrix (w009 (a hA) (b hB)) = decodeRows v013 := by
  rw [w009, map_pow, matrix_w003 hA hB, power004_4]

theorem matrix_w010 : toMatrix (w010 (a hA) (b hB)) = decodeRows v014 := by
  exact mul_certificate _ _ _ _ _ (matrix_w008 hA hB) (matrix_w009 hA hB) product011

theorem matrix_w011 : toMatrix (w011 (a hA) (b hB)) = decodeRows v015 := by
  exact mul_certificate _ _ _ _ _ (matrix_w010 hA hB) (matrix_w007 hA hB) product012

theorem matrix_w012 : toMatrix (w012 (a hA) (b hB)) = decodeRows v016 := by
  exact mul_certificate _ _ _ _ _ (matrix_w000 hA hB) (matrix_w011 hA hB) product013

theorem matrix_w013 : toMatrix (w013 (a hA) (b hB)) = decodeRows v019 := by
  rw [w013, map_pow, matrix_w012 hA hB, power016_6]

theorem matrix_w014 : toMatrix (w014 (a hA) (b hB)) = decodeRows v020 := by
  exact mul_certificate _ _ _ _ _ (matrix_w012 hA hB) (matrix_w011 hA hB) product017

theorem matrix_w015 : toMatrix (w015 (a hA) (b hB)) = decodeRows v022 := by
  rw [w015, map_pow, matrix_w014 hA hB, power020_3]

theorem matrix_w016 : toMatrix (w016 (a hA) (b hB)) = decodeRows v017 := by
  exact mul_certificate _ _ _ _ _ (matrix_w012 hA hB) (matrix_w012 hA hB) product014

theorem matrix_w017 : toMatrix (w017 (a hA) (b hB)) = decodeRows v023 := by
  exact mul_certificate _ _ _ _ _ (matrix_w015 hA hB) (matrix_w016 hA hB) product020

theorem matrix_w018 : toMatrix (w018 (a hA) (b hB)) = decodeRows v024 := by
  exact mul_certificate _ _ _ _ _ (matrix_w013 hA hB) (matrix_w017 hA hB) product021

theorem matrix_w019 : toMatrix (w019 (a hA) (b hB)) = decodeRows v027 := by
  rw [w019, map_pow, matrix_w018 hA hB, power024_8]

theorem matrix_w020 : toMatrix (w020 (a hA) (b hB)) = decodeRows v031 := by
  rw [w020, map_pow, matrix_w018 hA hB, power024_20]

theorem matrix_w021 : toMatrix (w021 (a hA) (b hB)) = decodeRows v032 := by
  exact mul_certificate _ _ _ _ _ (matrix_w001 hA hB) (matrix_w020 hA hB) product029

theorem matrix_w022 : toMatrix (w022 (a hA) (b hB)) = decodeRows v033 := by
  exact inv_certificate _ _ _ (matrix_w021 hA hB) (product030.trans decode_identity)

theorem matrix_w023 : toMatrix (w023 (a hA) (b hB)) = decodeRows v034 := by
  exact mul_certificate _ _ _ _ _ (matrix_w020 hA hB) (matrix_w001 hA hB) product031

theorem matrix_w024 : toMatrix (w024 (a hA) (b hB)) = decodeRows v035 := by
  exact mul_certificate _ _ _ _ _ (matrix_w022 hA hB) (matrix_w023 hA hB) product032

theorem matrix_w025 : toMatrix (w025 (a hA) (b hB)) = decodeRows v037 := by
  rw [w025, map_pow, matrix_w024 hA hB, power035_3]

theorem matrix_w026 : toMatrix (w026 (a hA) (b hB)) = decodeRows v038 := by
  exact inv_certificate _ _ _ (matrix_w018 hA hB) (product035.trans decode_identity)

theorem matrix_w027 : toMatrix (w027 (a hA) (b hB)) = decodeRows v039 := by
  exact mul_certificate _ _ _ _ _ (matrix_w026 hA hB) (matrix_w025 hA hB) product036

theorem matrix_w028 : toMatrix (w028 (a hA) (b hB)) = decodeRows v040 := by
  exact mul_certificate _ _ _ _ _ (matrix_w025 hA hB) (matrix_w027 hA hB) product037

theorem matrix_w029 : toMatrix (w029 (a hA) (b hB)) = decodeRows v041 := by
  exact mul_certificate _ _ _ _ _ (matrix_w019 hA hB) (matrix_w028 hA hB) product038

theorem matrix_w030 : toMatrix (w030 (a hA) (b hB)) = decodeRows v042 := by
  exact inv_certificate _ _ _ (matrix_w029 hA hB) (product039.trans decode_identity)

theorem matrix_w031 : toMatrix (w031 (a hA) (b hB)) = decodeRows v043 := by
  exact mul_certificate _ _ _ _ _ (matrix_w018 hA hB) (matrix_w025 hA hB) product040

theorem matrix_w032 : toMatrix (w032 (a hA) (b hB)) = decodeRows v044 := by
  exact mul_certificate _ _ _ _ _ (matrix_w018 hA hB) (matrix_w031 hA hB) product041

theorem matrix_w033 : toMatrix (w033 (a hA) (b hB)) = decodeRows v048 := by
  rw [w033, map_pow, matrix_w032 hA hB, power044_7]

theorem matrix_w034 : toMatrix (w034 (a hA) (b hB)) = decodeRows v049 := by
  exact mul_certificate _ _ _ _ _ (matrix_w030 hA hB) (matrix_w033 hA hB) product046

theorem matrix_w035 : toMatrix (w035 (a hA) (b hB)) = decodeRows v050 := by
  exact mul_certificate _ _ _ _ _ (matrix_w034 hA hB) (matrix_w029 hA hB) product047

theorem matrix_w036 : toMatrix (w036 (a hA) (b hB)) = decodeRows v051 := by
  exact mul_certificate _ _ _ _ _ (matrix_w000 hA hB) (matrix_w018 hA hB) product048

theorem matrix_w037 : toMatrix (w037 (a hA) (b hB)) = decodeRows v057 := by
  rw [w037, map_pow, matrix_w036 hA hB, power051_15]

theorem matrix_w038 : toMatrix (w038 (a hA) (b hB)) = decodeRows v058 := by
  exact mul_certificate _ _ _ _ _ (matrix_w035 hA hB) (matrix_w037 hA hB) product055

theorem matrix_w039 : toMatrix (w039 (a hA) (b hB)) = decodeRows v059 := by
  rw [w039, map_pow, matrix_w038 hA hB, power058_2]

theorem matrix_w040 : toMatrix (w040 (a hA) (b hB)) = decodeRows v060 := by
  exact inv_certificate _ _ _ (matrix_w039 hA hB) (product057.trans decode_identity)

theorem matrix_w041 : toMatrix (w041 (a hA) (b hB)) = decodeRows v061 := by
  exact inv_certificate _ _ _ (matrix_w036 hA hB) (product058.trans decode_identity)

theorem matrix_w042 : toMatrix (w042 (a hA) (b hB)) = decodeRows v062 := by
  exact mul_certificate _ _ _ _ _ (matrix_w041 hA hB) (matrix_w039 hA hB) product059

theorem matrix_w043 : toMatrix (w043 (a hA) (b hB)) = decodeRows v063 := by
  exact mul_certificate _ _ _ _ _ (matrix_w042 hA hB) (matrix_w036 hA hB) product060

theorem matrix_w044 : toMatrix (w044 (a hA) (b hB)) = decodeRows v064 := by
  exact inv_certificate _ _ _ (matrix_w043 hA hB) (product061.trans decode_identity)

theorem matrix_w045 : toMatrix (w045 (a hA) (b hB)) = decodeRows v065 := by
  exact mul_certificate _ _ _ _ _ (matrix_w040 hA hB) (matrix_w044 hA hB) product062

theorem matrix_w046 : toMatrix (w046 (a hA) (b hB)) = decodeRows v066 := by
  exact mul_certificate _ _ _ _ _ (matrix_w045 hA hB) (matrix_w039 hA hB) product063

theorem matrix_w047 : toMatrix (w047 (a hA) (b hB)) = decodeRows v067 := by
  exact mul_certificate _ _ _ _ _ (matrix_w046 hA hB) (matrix_w043 hA hB) product064

theorem matrix_w048 : toMatrix (w048 (a hA) (b hB)) = decodeRows v068 := by
  exact mul_certificate _ _ _ _ _ (matrix_w003 hA hB) (matrix_w000 hA hB) product065

theorem matrix_w049 : toMatrix (w049 (a hA) (b hB)) = decodeRows v069 := by
  exact mul_certificate _ _ _ _ _ (matrix_w048 hA hB) (matrix_w001 hA hB) product066

theorem matrix_w050 : toMatrix (w050 (a hA) (b hB)) = decodeRows v070 := by
  exact mul_certificate _ _ _ _ _ (matrix_w049 hA hB) (matrix_w000 hA hB) product067

theorem matrix_w051 : toMatrix (w051 (a hA) (b hB)) = decodeRows v071 := by
  exact mul_certificate _ _ _ _ _ (matrix_w050 hA hB) (matrix_w001 hA hB) product068

theorem matrix_w052 : toMatrix (w052 (a hA) (b hB)) = decodeRows v072 := by
  exact mul_certificate _ _ _ _ _ (matrix_w051 hA hB) (matrix_w000 hA hB) product069

theorem matrix_w053 : toMatrix (w053 (a hA) (b hB)) = decodeRows v073 := by
  exact mul_certificate _ _ _ _ _ (matrix_w052 hA hB) (matrix_w001 hA hB) product070

theorem matrix_w054 : toMatrix (w054 (a hA) (b hB)) = decodeRows v074 := by
  exact mul_certificate _ _ _ _ _ (matrix_w053 hA hB) (matrix_w001 hA hB) product071

theorem matrix_w055 : toMatrix (w055 (a hA) (b hB)) = decodeRows v077 := by
  rw [w055, map_pow, matrix_w054 hA hB, power074_6]

theorem matrix_w056 : toMatrix (w056 (a hA) (b hB)) = decodeRows v084 := by
  rw [w056, map_pow, matrix_w054 hA hB, power074_33]

theorem matrix_w057 : toMatrix (w057 (a hA) (b hB)) = decodeRows v085 := by
  exact mul_certificate _ _ _ _ _ (matrix_w001 hA hB) (matrix_w000 hA hB) product082

theorem matrix_w058 : toMatrix (w058 (a hA) (b hB)) = decodeRows v002 := by
  exact mul_certificate _ _ _ _ _ (matrix_w057 hA hB) (matrix_w000 hA hB) product083

theorem matrix_w059 : toMatrix (w059 (a hA) (b hB)) = decodeRows v085 := by
  exact mul_certificate _ _ _ _ _ (matrix_w058 hA hB) (matrix_w000 hA hB) product082

theorem matrix_w060 : toMatrix (w060 (a hA) (b hB)) = decodeRows v002 := by
  exact mul_certificate _ _ _ _ _ (matrix_w059 hA hB) (matrix_w000 hA hB) product083

theorem matrix_w061 : toMatrix (w061 (a hA) (b hB)) = decodeRows v085 := by
  exact mul_certificate _ _ _ _ _ (matrix_w060 hA hB) (matrix_w000 hA hB) product082

theorem matrix_w062 : toMatrix (w062 (a hA) (b hB)) = decodeRows v086 := by
  exact mul_certificate _ _ _ _ _ (matrix_w061 hA hB) (matrix_w001 hA hB) product084

theorem matrix_w063 : toMatrix (w063 (a hA) (b hB)) = decodeRows v087 := by
  exact mul_certificate _ _ _ _ _ (matrix_w062 hA hB) (matrix_w001 hA hB) product085

theorem matrix_w064 : toMatrix (w064 (a hA) (b hB)) = decodeRows v088 := by
  exact mul_certificate _ _ _ _ _ (matrix_w063 hA hB) (matrix_w000 hA hB) product086

theorem matrix_w065 : toMatrix (w065 (a hA) (b hB)) = decodeRows v089 := by
  exact mul_certificate _ _ _ _ _ (matrix_w064 hA hB) (matrix_w001 hA hB) product087

theorem matrix_w066 : toMatrix (w066 (a hA) (b hB)) = decodeRows v090 := by
  exact mul_certificate _ _ _ _ _ (matrix_w065 hA hB) (matrix_w000 hA hB) product088

theorem matrix_w067 : toMatrix (w067 (a hA) (b hB)) = decodeRows v089 := by
  exact mul_certificate _ _ _ _ _ (matrix_w066 hA hB) (matrix_w000 hA hB) product089

theorem matrix_w068 : toMatrix (w068 (a hA) (b hB)) = decodeRows v091 := by
  exact mul_certificate _ _ _ _ _ (matrix_w067 hA hB) (matrix_w001 hA hB) product090

theorem matrix_w069 : toMatrix (w069 (a hA) (b hB)) = decodeRows v092 := by
  exact mul_certificate _ _ _ _ _ (matrix_w068 hA hB) (matrix_w001 hA hB) product091

theorem matrix_w070 : toMatrix (w070 (a hA) (b hB)) = decodeRows v088 := by
  exact mul_certificate _ _ _ _ _ (matrix_w069 hA hB) (matrix_w001 hA hB) product092

theorem matrix_w071 : toMatrix (w071 (a hA) (b hB)) = decodeRows v093 := by
  exact inv_certificate _ _ _ (matrix_w070 hA hB) (product093.trans decode_identity)

theorem matrix_w072 : toMatrix (w072 (a hA) (b hB)) = decodeRows v094 := by
  exact mul_certificate _ _ _ _ _ (matrix_w071 hA hB) (matrix_w020 hA hB) product094

theorem matrix_w073 : toMatrix (w073 (a hA) (b hB)) = decodeRows v095 := by
  exact mul_certificate _ _ _ _ _ (matrix_w072 hA hB) (matrix_w070 hA hB) product095

theorem matrix_w074 : toMatrix (w074 (a hA) (b hB)) = decodeRows v096 := by
  exact mul_certificate _ _ _ _ _ (matrix_w056 hA hB) (matrix_w073 hA hB) product096

theorem matrix_w075 : toMatrix (w075 (a hA) (b hB)) = decodeRows v099 := by
  rw [w075, map_pow, matrix_w074 hA hB, power096_6]

theorem matrix_w076 : toMatrix (w076 (a hA) (b hB)) = decodeRows v100 := by
  exact mul_certificate _ _ _ _ _ (matrix_w075 hA hB) (matrix_w071 hA hB) product100

theorem matrix_w077 : toMatrix (w077 (a hA) (b hB)) = decodeRows v000 := by
  exact decode_identity.symm

theorem matrix_w078 : toMatrix (w078 (a hA) (b hB)) = decodeRows v024 := by
  exact mul_certificate _ _ _ _ _ (matrix_w077 hA hB) (matrix_w018 hA hB) product101

theorem matrix_w079 : toMatrix (w079 (a hA) (b hB)) = decodeRows v025 := by
  exact mul_certificate _ _ _ _ _ (matrix_w078 hA hB) (matrix_w018 hA hB) product022

theorem matrix_w080 : toMatrix (w080 (a hA) (b hB)) = decodeRows v028 := by
  exact mul_certificate _ _ _ _ _ (matrix_w079 hA hB) (matrix_w018 hA hB) product102

theorem matrix_w081 : toMatrix (w081 (a hA) (b hB)) = decodeRows v026 := by
  exact mul_certificate _ _ _ _ _ (matrix_w080 hA hB) (matrix_w018 hA hB) product103

theorem matrix_w082 : toMatrix (w082 (a hA) (b hB)) = decodeRows v101 := by
  exact mul_certificate _ _ _ _ _ (matrix_w081 hA hB) (matrix_w025 hA hB) product104

theorem matrix_w083 : toMatrix (w083 (a hA) (b hB)) = decodeRows v102 := by
  exact mul_certificate _ _ _ _ _ (matrix_w082 hA hB) (matrix_w018 hA hB) product105

theorem matrix_w084 : toMatrix (w084 (a hA) (b hB)) = decodeRows v103 := by
  exact mul_certificate _ _ _ _ _ (matrix_w083 hA hB) (matrix_w025 hA hB) product106

theorem matrix_w085 : toMatrix (w085 (a hA) (b hB)) = decodeRows v104 := by
  exact mul_certificate _ _ _ _ _ (matrix_w084 hA hB) (matrix_w026 hA hB) product107

theorem matrix_w086 : toMatrix (w086 (a hA) (b hB)) = decodeRows v105 := by
  exact mul_certificate _ _ _ _ _ (matrix_w085 hA hB) (matrix_w026 hA hB) product108

theorem matrix_w087 : toMatrix (w087 (a hA) (b hB)) = decodeRows v106 := by
  exact mul_certificate _ _ _ _ _ (matrix_w086 hA hB) (matrix_w026 hA hB) product109

theorem matrix_w088 : toMatrix (w088 (a hA) (b hB)) = decodeRows v107 := by
  exact mul_certificate _ _ _ _ _ (matrix_w087 hA hB) (matrix_w025 hA hB) product110

theorem matrix_w089 : toMatrix (w089 (a hA) (b hB)) = decodeRows v108 := by
  exact mul_certificate _ _ _ _ _ (matrix_w076 hA hB) (matrix_w088 hA hB) product111

theorem matrix_w090 : toMatrix (w090 (a hA) (b hB)) = decodeRows v037 := by
  exact mul_certificate _ _ _ _ _ (matrix_w077 hA hB) (matrix_w025 hA hB) product112

theorem matrix_w091 : toMatrix (w091 (a hA) (b hB)) = decodeRows v109 := by
  exact mul_certificate _ _ _ _ _ (matrix_w090 hA hB) (matrix_w018 hA hB) product113

theorem matrix_w092 : toMatrix (w092 (a hA) (b hB)) = decodeRows v110 := by
  exact mul_certificate _ _ _ _ _ (matrix_w091 hA hB) (matrix_w025 hA hB) product114

theorem matrix_w093 : toMatrix (w093 (a hA) (b hB)) = decodeRows v111 := by
  exact mul_certificate _ _ _ _ _ (matrix_w092 hA hB) (matrix_w018 hA hB) product115

theorem matrix_w094 : toMatrix (w094 (a hA) (b hB)) = decodeRows v112 := by
  exact mul_certificate _ _ _ _ _ (matrix_w093 hA hB) (matrix_w018 hA hB) product116

theorem matrix_w095 : toMatrix (w095 (a hA) (b hB)) = decodeRows v113 := by
  exact mul_certificate _ _ _ _ _ (matrix_w094 hA hB) (matrix_w025 hA hB) product117

theorem matrix_w096 : toMatrix (w096 (a hA) (b hB)) = decodeRows v114 := by
  exact mul_certificate _ _ _ _ _ (matrix_w095 hA hB) (matrix_w026 hA hB) product118

theorem matrix_w097 : toMatrix (w097 (a hA) (b hB)) = decodeRows v115 := by
  exact mul_certificate _ _ _ _ _ (matrix_w096 hA hB) (matrix_w025 hA hB) product119

theorem matrix_w098 : toMatrix (w098 (a hA) (b hB)) = decodeRows v116 := by
  exact mul_certificate _ _ _ _ _ (matrix_w097 hA hB) (matrix_w026 hA hB) product120

theorem matrix_w099 : toMatrix (w099 (a hA) (b hB)) = decodeRows v117 := by
  exact mul_certificate _ _ _ _ _ (matrix_w098 hA hB) (matrix_w026 hA hB) product121

theorem matrix_w100 : toMatrix (w100 (a hA) (b hB)) = decodeRows v118 := by
  exact mul_certificate _ _ _ _ _ (matrix_w099 hA hB) (matrix_w026 hA hB) product122

theorem matrix_w101 : toMatrix (w101 (a hA) (b hB)) = decodeRows v119 := by
  exact mul_certificate _ _ _ _ _ (matrix_w100 hA hB) (matrix_w026 hA hB) product123

theorem matrix_w102 : toMatrix (w102 (a hA) (b hB)) = decodeRows v120 := by
  exact mul_certificate _ _ _ _ _ (matrix_w101 hA hB) (matrix_w026 hA hB) product124

theorem matrix_w103 : toMatrix (w103 (a hA) (b hB)) = decodeRows v121 := by
  exact inv_certificate _ _ _ (matrix_w102 hA hB) (product125.trans decode_identity)

theorem matrix_w104 : toMatrix (w104 (a hA) (b hB)) = decodeRows v122 := by
  exact mul_certificate _ _ _ _ _ (matrix_w089 hA hB) (matrix_w103 hA hB) product126

theorem matrix_w105 : toMatrix (w105 (a hA) (b hB)) = decodeRows v126 := by
  rw [w105, map_pow, matrix_w047 hA hB, power067_7]

theorem matrix_w106 : toMatrix (w106 (a hA) (b hB)) = decodeRows v127 := by
  exact mul_certificate _ _ _ _ _ (matrix_w104 hA hB) (matrix_w105 hA hB) product131

theorem matrix_w107 : toMatrix (w107 (a hA) (b hB)) = decodeRows v128 := by
  exact inv_certificate _ _ _ (matrix_w104 hA hB) (product132.trans decode_identity)

theorem matrix_w108 : toMatrix (w108 (a hA) (b hB)) = decodeRows v077 := by
  exact mul_certificate _ _ _ _ _ (matrix_w106 hA hB) (matrix_w107 hA hB) product133

theorem matrix_w109 : toMatrix (w109 (a hA) (b hB)) = decodeRows v129 := by
  exact mul_certificate _ _ _ _ _ (matrix_w054 hA hB) (matrix_w000 hA hB) product134

theorem matrix_w110 : toMatrix (w110 (a hA) (b hB)) = decodeRows v130 := by
  exact mul_certificate _ _ _ _ _ (matrix_w109 hA hB) (matrix_w001 hA hB) product135

theorem matrix_w111 : toMatrix (w111 (a hA) (b hB)) = decodeRows v131 := by
  exact mul_certificate _ _ _ _ _ (matrix_w110 hA hB) (matrix_w000 hA hB) product136

theorem matrix_w112 : toMatrix (w112 (a hA) (b hB)) = decodeRows v132 := by
  exact mul_certificate _ _ _ _ _ (matrix_w111 hA hB) (matrix_w001 hA hB) product137

theorem matrix_w113 : toMatrix (w113 (a hA) (b hB)) = decodeRows v133 := by
  exact mul_certificate _ _ _ _ _ (matrix_w112 hA hB) (matrix_w000 hA hB) product138

theorem matrix_w114 : toMatrix (w114 (a hA) (b hB)) = decodeRows v134 := by
  exact mul_certificate _ _ _ _ _ (matrix_w113 hA hB) (matrix_w001 hA hB) product139

theorem matrix_w115 : toMatrix (w115 (a hA) (b hB)) = decodeRows v135 := by
  exact mul_certificate _ _ _ _ _ (matrix_w114 hA hB) (matrix_w001 hA hB) product140

theorem matrix_w116 : toMatrix (w116 (a hA) (b hB)) = decodeRows v136 := by
  exact mul_certificate _ _ _ _ _ (matrix_w115 hA hB) (matrix_w000 hA hB) product141

theorem matrix_w117 : toMatrix (w117 (a hA) (b hB)) = decodeRows v137 := by
  exact mul_certificate _ _ _ _ _ (matrix_w116 hA hB) (matrix_w001 hA hB) product142

theorem matrix_w118 : toMatrix (w118 (a hA) (b hB)) = decodeRows v138 := by
  exact mul_certificate _ _ _ _ _ (matrix_w117 hA hB) (matrix_w001 hA hB) product143

theorem matrix_w119 : toMatrix (w119 (a hA) (b hB)) = decodeRows v139 := by
  exact mul_certificate _ _ _ _ _ (matrix_w118 hA hB) (matrix_w000 hA hB) product144

theorem matrix_w120 : toMatrix (w120 (a hA) (b hB)) = decodeRows v140 := by
  exact mul_certificate _ _ _ _ _ (matrix_w119 hA hB) (matrix_w001 hA hB) product145

theorem matrix_w121 : toMatrix (w121 (a hA) (b hB)) = decodeRows v141 := by
  exact mul_certificate _ _ _ _ _ (matrix_w120 hA hB) (matrix_w000 hA hB) product146

theorem matrix_w122 : toMatrix (w122 (a hA) (b hB)) = decodeRows v142 := by
  exact mul_certificate _ _ _ _ _ (matrix_w121 hA hB) (matrix_w001 hA hB) product147

theorem matrix_w123 : toMatrix (w123 (a hA) (b hB)) = decodeRows v143 := by
  exact mul_certificate _ _ _ _ _ (matrix_w122 hA hB) (matrix_w000 hA hB) product148

theorem matrix_w124 : toMatrix (w124 (a hA) (b hB)) = decodeRows v144 := by
  exact mul_certificate _ _ _ _ _ (matrix_w123 hA hB) (matrix_w001 hA hB) product149

theorem matrix_w125 : toMatrix (w125 (a hA) (b hB)) = decodeRows v145 := by
  exact mul_certificate _ _ _ _ _ (matrix_w124 hA hB) (matrix_w001 hA hB) product150

theorem matrix_w126 : toMatrix (w126 (a hA) (b hB)) = decodeRows v146 := by
  rw [w126, map_pow, matrix_w125 hA hB, power145_2]

theorem matrix_w127 : toMatrix (w127 (a hA) (b hB)) = decodeRows v150 := by
  rw [w127, map_pow, matrix_w125 hA hB, power145_11]

theorem matrix_w128 : toMatrix (w128 (a hA) (b hB)) = decodeRows v000 := by
  exact mul_certificate _ _ _ _ _ (matrix_w000 hA hB) (matrix_w000 hA hB) product156

theorem matrix_w129 : toMatrix (w129 (a hA) (b hB)) = decodeRows v002 := by
  exact mul_certificate _ _ _ _ _ (matrix_w128 hA hB) (matrix_w001 hA hB) product157

theorem matrix_w130 : toMatrix (w130 (a hA) (b hB)) = decodeRows v085 := by
  exact mul_certificate _ _ _ _ _ (matrix_w129 hA hB) (matrix_w000 hA hB) product082

theorem matrix_w131 : toMatrix (w131 (a hA) (b hB)) = decodeRows v086 := by
  exact mul_certificate _ _ _ _ _ (matrix_w130 hA hB) (matrix_w001 hA hB) product084

theorem matrix_w132 : toMatrix (w132 (a hA) (b hB)) = decodeRows v087 := by
  exact mul_certificate _ _ _ _ _ (matrix_w131 hA hB) (matrix_w001 hA hB) product085

theorem matrix_w133 : toMatrix (w133 (a hA) (b hB)) = decodeRows v088 := by
  exact mul_certificate _ _ _ _ _ (matrix_w132 hA hB) (matrix_w000 hA hB) product086

theorem matrix_w134 : toMatrix (w134 (a hA) (b hB)) = decodeRows v089 := by
  exact mul_certificate _ _ _ _ _ (matrix_w133 hA hB) (matrix_w001 hA hB) product087

theorem matrix_w135 : toMatrix (w135 (a hA) (b hB)) = decodeRows v091 := by
  exact mul_certificate _ _ _ _ _ (matrix_w134 hA hB) (matrix_w001 hA hB) product090

theorem matrix_w136 : toMatrix (w136 (a hA) (b hB)) = decodeRows v092 := by
  exact mul_certificate _ _ _ _ _ (matrix_w135 hA hB) (matrix_w001 hA hB) product091

theorem matrix_w137 : toMatrix (w137 (a hA) (b hB)) = decodeRows v151 := by
  exact mul_certificate _ _ _ _ _ (matrix_w136 hA hB) (matrix_w000 hA hB) product158

theorem matrix_w138 : toMatrix (w138 (a hA) (b hB)) = decodeRows v152 := by
  exact mul_certificate _ _ _ _ _ (matrix_w137 hA hB) (matrix_w001 hA hB) product159

theorem matrix_w139 : toMatrix (w139 (a hA) (b hB)) = decodeRows v153 := by
  exact mul_certificate _ _ _ _ _ (matrix_w138 hA hB) (matrix_w000 hA hB) product160

theorem matrix_w140 : toMatrix (w140 (a hA) (b hB)) = decodeRows v154 := by
  exact mul_certificate _ _ _ _ _ (matrix_w139 hA hB) (matrix_w001 hA hB) product161

theorem matrix_w141 : toMatrix (w141 (a hA) (b hB)) = decodeRows v155 := by
  exact mul_certificate _ _ _ _ _ (matrix_w140 hA hB) (matrix_w001 hA hB) product162

theorem matrix_w142 : toMatrix (w142 (a hA) (b hB)) = decodeRows v156 := by
  exact inv_certificate _ _ _ (matrix_w141 hA hB) (product163.trans decode_identity)

theorem matrix_w143 : toMatrix (w143 (a hA) (b hB)) = decodeRows v050 := by
  exact mul_certificate _ _ _ _ _ (matrix_w077 hA hB) (matrix_w035 hA hB) product164

theorem matrix_w144 : toMatrix (w144 (a hA) (b hB)) = decodeRows v157 := by
  exact mul_certificate _ _ _ _ _ (matrix_w143 hA hB) (matrix_w035 hA hB) product165

theorem matrix_w145 : toMatrix (w145 (a hA) (b hB)) = decodeRows v158 := by
  exact mul_certificate _ _ _ _ _ (matrix_w144 hA hB) (matrix_w036 hA hB) product166

theorem matrix_w146 : toMatrix (w146 (a hA) (b hB)) = decodeRows v159 := by
  exact mul_certificate _ _ _ _ _ (matrix_w145 hA hB) (matrix_w035 hA hB) product167

theorem matrix_w147 : toMatrix (w147 (a hA) (b hB)) = decodeRows v160 := by
  exact mul_certificate _ _ _ _ _ (matrix_w146 hA hB) (matrix_w036 hA hB) product168

theorem matrix_w148 : toMatrix (w148 (a hA) (b hB)) = decodeRows v161 := by
  exact mul_certificate _ _ _ _ _ (matrix_w036 hA hB) (matrix_w035 hA hB) product169

theorem matrix_w149 : toMatrix (w149 (a hA) (b hB)) = decodeRows v162 := by
  exact mul_certificate _ _ _ _ _ (matrix_w148 hA hB) (matrix_w036 hA hB) product170

theorem matrix_w150 : toMatrix (w150 (a hA) (b hB)) = decodeRows v163 := by
  exact mul_certificate _ _ _ _ _ (matrix_w149 hA hB) (matrix_w036 hA hB) product171

theorem matrix_w151 : toMatrix (w151 (a hA) (b hB)) = decodeRows v166 := by
  rw [w151, map_pow, matrix_w150 hA hB, power163_5]

theorem matrix_w152 : toMatrix (w152 (a hA) (b hB)) = decodeRows v167 := by
  exact mul_certificate _ _ _ _ _ (matrix_w147 hA hB) (matrix_w151 hA hB) product175

theorem matrix_w153 : toMatrix (w153 (a hA) (b hB)) = decodeRows v168 := by
  exact inv_certificate _ _ _ (matrix_w147 hA hB) (product176.trans decode_identity)

theorem matrix_w154 : toMatrix (w154 (a hA) (b hB)) = decodeRows v169 := by
  exact mul_certificate _ _ _ _ _ (matrix_w152 hA hB) (matrix_w153 hA hB) product177

theorem matrix_w155 : toMatrix (w155 (a hA) (b hB)) = decodeRows v170 := by
  exact mul_certificate _ _ _ _ _ (matrix_w142 hA hB) (matrix_w154 hA hB) product178

theorem matrix_w156 : toMatrix (w156 (a hA) (b hB)) = decodeRows v171 := by
  exact mul_certificate _ _ _ _ _ (matrix_w155 hA hB) (matrix_w141 hA hB) product179

theorem matrix_w157 : toMatrix (w157 (a hA) (b hB)) = decodeRows v172 := by
  exact mul_certificate _ _ _ _ _ (matrix_w127 hA hB) (matrix_w156 hA hB) product180

theorem matrix_w158 : toMatrix (w158 (a hA) (b hB)) = decodeRows v179 := by
  rw [w158, map_pow, matrix_w157 hA hB, power172_19]

theorem matrix_w159 : toMatrix (w159 (a hA) (b hB)) = decodeRows v180 := by
  exact mul_certificate _ _ _ _ _ (matrix_w158 hA hB) (matrix_w142 hA hB) product188

theorem matrix_w160 : toMatrix (w160 (a hA) (b hB)) = decodeRows v181 := by
  exact mul_certificate _ _ _ _ _ (matrix_w002 hA hB) (matrix_w000 hA hB) product189

theorem matrix_w161 : toMatrix (w161 (a hA) (b hB)) = decodeRows v003 := by
  exact mul_certificate _ _ _ _ _ (matrix_w160 hA hB) (matrix_w000 hA hB) product190

theorem matrix_w162 : toMatrix (w162 (a hA) (b hB)) = decodeRows v181 := by
  exact mul_certificate _ _ _ _ _ (matrix_w161 hA hB) (matrix_w000 hA hB) product189

theorem matrix_w163 : toMatrix (w163 (a hA) (b hB)) = decodeRows v182 := by
  exact mul_certificate _ _ _ _ _ (matrix_w162 hA hB) (matrix_w001 hA hB) product191

theorem matrix_w164 : toMatrix (w164 (a hA) (b hB)) = decodeRows v183 := by
  exact mul_certificate _ _ _ _ _ (matrix_w163 hA hB) (matrix_w000 hA hB) product192

theorem matrix_w165 : toMatrix (w165 (a hA) (b hB)) = decodeRows v182 := by
  exact mul_certificate _ _ _ _ _ (matrix_w164 hA hB) (matrix_w000 hA hB) product193

theorem matrix_w166 : toMatrix (w166 (a hA) (b hB)) = decodeRows v005 := by
  exact mul_certificate _ _ _ _ _ (matrix_w165 hA hB) (matrix_w001 hA hB) product194

theorem matrix_w167 : toMatrix (w167 (a hA) (b hB)) = decodeRows v184 := by
  exact mul_certificate _ _ _ _ _ (matrix_w166 hA hB) (matrix_w000 hA hB) product195

theorem matrix_w168 : toMatrix (w168 (a hA) (b hB)) = decodeRows v185 := by
  exact mul_certificate _ _ _ _ _ (matrix_w167 hA hB) (matrix_w001 hA hB) product196

theorem matrix_w169 : toMatrix (w169 (a hA) (b hB)) = decodeRows v186 := by
  exact mul_certificate _ _ _ _ _ (matrix_w168 hA hB) (matrix_w001 hA hB) product197

theorem matrix_w170 : toMatrix (w170 (a hA) (b hB)) = decodeRows v187 := by
  exact mul_certificate _ _ _ _ _ (matrix_w169 hA hB) (matrix_w000 hA hB) product198

theorem matrix_w171 : toMatrix (w171 (a hA) (b hB)) = decodeRows v186 := by
  exact mul_certificate _ _ _ _ _ (matrix_w170 hA hB) (matrix_w000 hA hB) product199

theorem matrix_w172 : toMatrix (w172 (a hA) (b hB)) = decodeRows v187 := by
  exact mul_certificate _ _ _ _ _ (matrix_w171 hA hB) (matrix_w000 hA hB) product198

theorem matrix_w173 : toMatrix (w173 (a hA) (b hB)) = decodeRows v188 := by
  exact mul_certificate _ _ _ _ _ (matrix_w172 hA hB) (matrix_w001 hA hB) product200

theorem matrix_w174 : toMatrix (w174 (a hA) (b hB)) = decodeRows v189 := by
  exact mul_certificate _ _ _ _ _ (matrix_w173 hA hB) (matrix_w000 hA hB) product201

theorem matrix_w175 : toMatrix (w175 (a hA) (b hB)) = decodeRows v188 := by
  exact mul_certificate _ _ _ _ _ (matrix_w174 hA hB) (matrix_w000 hA hB) product202

theorem matrix_w176 : toMatrix (w176 (a hA) (b hB)) = decodeRows v190 := by
  exact mul_certificate _ _ _ _ _ (matrix_w175 hA hB) (matrix_w001 hA hB) product203

theorem matrix_w177 : toMatrix (w177 (a hA) (b hB)) = decodeRows v191 := by
  exact mul_certificate _ _ _ _ _ (matrix_w176 hA hB) (matrix_w001 hA hB) product204

theorem matrix_w178 : toMatrix (w178 (a hA) (b hB)) = decodeRows v192 := by
  exact mul_certificate _ _ _ _ _ (matrix_w177 hA hB) (matrix_w000 hA hB) product205

theorem matrix_w179 : toMatrix (w179 (a hA) (b hB)) = decodeRows v191 := by
  exact mul_certificate _ _ _ _ _ (matrix_w178 hA hB) (matrix_w000 hA hB) product206

theorem matrix_w180 : toMatrix (w180 (a hA) (b hB)) = decodeRows v193 := by
  exact inv_certificate _ _ _ (matrix_w179 hA hB) (product207.trans decode_identity)

theorem matrix_w181 : toMatrix (w181 (a hA) (b hB)) = decodeRows v194 := by
  exact mul_certificate _ _ _ _ _ (matrix_w180 hA hB) (matrix_w154 hA hB) product208

theorem matrix_w182 : toMatrix (w182 (a hA) (b hB)) = decodeRows v195 := by
  exact mul_certificate _ _ _ _ _ (matrix_w181 hA hB) (matrix_w179 hA hB) product209

theorem matrix_w183 : toMatrix (w183 (a hA) (b hB)) = decodeRows v196 := by
  exact mul_certificate _ _ _ _ _ (matrix_w154 hA hB) (matrix_w182 hA hB) product210

theorem matrix_w184 : toMatrix (w184 (a hA) (b hB)) = decodeRows v200 := by
  rw [w184, map_pow, matrix_w183 hA hB, power196_12]

theorem matrix_w185 : toMatrix (w185 (a hA) (b hB)) = decodeRows v201 := by
  exact mul_certificate _ _ _ _ _ (matrix_w184 hA hB) (matrix_w180 hA hB) product215

theorem matrix_w186 : toMatrix (w186 (a hA) (b hB)) = decodeRows v201 := by
  exact mul_certificate _ _ _ _ _ (matrix_w077 hA hB) (matrix_w185 hA hB) product216

theorem matrix_w187 : toMatrix (w187 (a hA) (b hB)) = decodeRows v202 := by
  exact mul_certificate _ _ _ _ _ (matrix_w186 hA hB) (matrix_w185 hA hB) product217

theorem matrix_w188 : toMatrix (w188 (a hA) (b hB)) = decodeRows v203 := by
  exact mul_certificate _ _ _ _ _ (matrix_w187 hA hB) (matrix_w185 hA hB) product218

theorem matrix_w189 : toMatrix (w189 (a hA) (b hB)) = decodeRows v086 := by
  exact mul_certificate _ _ _ _ _ (matrix_w057 hA hB) (matrix_w001 hA hB) product084

theorem matrix_w190 : toMatrix (w190 (a hA) (b hB)) = decodeRows v087 := by
  exact mul_certificate _ _ _ _ _ (matrix_w189 hA hB) (matrix_w001 hA hB) product085

theorem matrix_w191 : toMatrix (w191 (a hA) (b hB)) = decodeRows v204 := by
  exact mul_certificate _ _ _ _ _ (matrix_w190 hA hB) (matrix_w001 hA hB) product219

theorem matrix_w192 : toMatrix (w192 (a hA) (b hB)) = decodeRows v085 := by
  exact mul_certificate _ _ _ _ _ (matrix_w191 hA hB) (matrix_w001 hA hB) product220

theorem matrix_w193 : toMatrix (w193 (a hA) (b hB)) = decodeRows v002 := by
  exact mul_certificate _ _ _ _ _ (matrix_w192 hA hB) (matrix_w000 hA hB) product083

theorem matrix_w194 : toMatrix (w194 (a hA) (b hB)) = decodeRows v085 := by
  exact mul_certificate _ _ _ _ _ (matrix_w193 hA hB) (matrix_w000 hA hB) product082

theorem matrix_w195 : toMatrix (w195 (a hA) (b hB)) = decodeRows v086 := by
  exact mul_certificate _ _ _ _ _ (matrix_w194 hA hB) (matrix_w001 hA hB) product084

theorem matrix_w196 : toMatrix (w196 (a hA) (b hB)) = decodeRows v205 := by
  exact mul_certificate _ _ _ _ _ (matrix_w195 hA hB) (matrix_w000 hA hB) product221

theorem matrix_w197 : toMatrix (w197 (a hA) (b hB)) = decodeRows v206 := by
  exact mul_certificate _ _ _ _ _ (matrix_w196 hA hB) (matrix_w001 hA hB) product222

theorem matrix_w198 : toMatrix (w198 (a hA) (b hB)) = decodeRows v207 := by
  exact mul_certificate _ _ _ _ _ (matrix_w197 hA hB) (matrix_w001 hA hB) product223

theorem matrix_w199 : toMatrix (w199 (a hA) (b hB)) = decodeRows v208 := by
  exact mul_certificate _ _ _ _ _ (matrix_w198 hA hB) (matrix_w000 hA hB) product224

theorem matrix_w200 : toMatrix (w200 (a hA) (b hB)) = decodeRows v209 := by
  exact mul_certificate _ _ _ _ _ (matrix_w199 hA hB) (matrix_w001 hA hB) product225

theorem matrix_w201 : toMatrix (w201 (a hA) (b hB)) = decodeRows v210 := by
  exact mul_certificate _ _ _ _ _ (matrix_w200 hA hB) (matrix_w001 hA hB) product226

theorem matrix_w202 : toMatrix (w202 (a hA) (b hB)) = decodeRows v211 := by
  exact mul_certificate _ _ _ _ _ (matrix_w201 hA hB) (matrix_w000 hA hB) product227

theorem matrix_w203 : toMatrix (w203 (a hA) (b hB)) = decodeRows v210 := by
  exact mul_certificate _ _ _ _ _ (matrix_w202 hA hB) (matrix_w000 hA hB) product228

theorem matrix_w204 : toMatrix (w204 (a hA) (b hB)) = decodeRows v211 := by
  exact mul_certificate _ _ _ _ _ (matrix_w203 hA hB) (matrix_w000 hA hB) product227

theorem matrix_w205 : toMatrix (w205 (a hA) (b hB)) = decodeRows v210 := by
  exact mul_certificate _ _ _ _ _ (matrix_w204 hA hB) (matrix_w000 hA hB) product228

theorem matrix_w206 : toMatrix (w206 (a hA) (b hB)) = decodeRows v212 := by
  exact mul_certificate _ _ _ _ _ (matrix_w205 hA hB) (matrix_w001 hA hB) product229

theorem matrix_w207 : toMatrix (w207 (a hA) (b hB)) = decodeRows v213 := by
  exact mul_certificate _ _ _ _ _ (matrix_w206 hA hB) (matrix_w000 hA hB) product230

theorem matrix_w208 : toMatrix (w208 (a hA) (b hB)) = decodeRows v212 := by
  exact mul_certificate _ _ _ _ _ (matrix_w207 hA hB) (matrix_w000 hA hB) product231

theorem matrix_w209 : toMatrix (w209 (a hA) (b hB)) = decodeRows v214 := by
  exact inv_certificate _ _ _ (matrix_w208 hA hB) (product232.trans decode_identity)

theorem matrix_w210 : toMatrix (w210 (a hA) (b hB)) = decodeRows v215 := by
  exact mul_certificate _ _ _ _ _ (matrix_w209 hA hB) (matrix_w154 hA hB) product233

theorem matrix_w211 : toMatrix (w211 (a hA) (b hB)) = decodeRows v216 := by
  exact mul_certificate _ _ _ _ _ (matrix_w210 hA hB) (matrix_w208 hA hB) product234

theorem matrix_w212 : toMatrix (w212 (a hA) (b hB)) = decodeRows v217 := by
  exact mul_certificate _ _ _ _ _ (matrix_w154 hA hB) (matrix_w211 hA hB) product235

theorem matrix_w213 : toMatrix (w213 (a hA) (b hB)) = decodeRows v222 := by
  rw [w213, map_pow, matrix_w212 hA hB, power217_20]

theorem matrix_w214 : toMatrix (w214 (a hA) (b hB)) = decodeRows v223 := by
  exact mul_certificate _ _ _ _ _ (matrix_w188 hA hB) (matrix_w213 hA hB) product241

theorem matrix_w215 : toMatrix (w215 (a hA) (b hB)) = decodeRows v001 := by
  exact mul_certificate _ _ _ _ _ (matrix_w128 hA hB) (matrix_w000 hA hB) product242

theorem matrix_w216 : toMatrix (w216 (a hA) (b hB)) = decodeRows v003 := by
  exact mul_certificate _ _ _ _ _ (matrix_w215 hA hB) (matrix_w001 hA hB) product000

theorem matrix_w217 : toMatrix (w217 (a hA) (b hB)) = decodeRows v181 := by
  exact mul_certificate _ _ _ _ _ (matrix_w216 hA hB) (matrix_w000 hA hB) product189

theorem matrix_w218 : toMatrix (w218 (a hA) (b hB)) = decodeRows v003 := by
  exact mul_certificate _ _ _ _ _ (matrix_w217 hA hB) (matrix_w000 hA hB) product190

theorem matrix_w219 : toMatrix (w219 (a hA) (b hB)) = decodeRows v004 := by
  exact mul_certificate _ _ _ _ _ (matrix_w218 hA hB) (matrix_w001 hA hB) product001

theorem matrix_w220 : toMatrix (w220 (a hA) (b hB)) = decodeRows v224 := by
  exact mul_certificate _ _ _ _ _ (matrix_w219 hA hB) (matrix_w001 hA hB) product243

theorem matrix_w221 : toMatrix (w221 (a hA) (b hB)) = decodeRows v225 := by
  exact mul_certificate _ _ _ _ _ (matrix_w220 hA hB) (matrix_w000 hA hB) product244

theorem matrix_w222 : toMatrix (w222 (a hA) (b hB)) = decodeRows v224 := by
  exact mul_certificate _ _ _ _ _ (matrix_w221 hA hB) (matrix_w000 hA hB) product245

theorem matrix_w223 : toMatrix (w223 (a hA) (b hB)) = decodeRows v001 := by
  exact mul_certificate _ _ _ _ _ (matrix_w222 hA hB) (matrix_w001 hA hB) product246

theorem matrix_w224 : toMatrix (w224 (a hA) (b hB)) = decodeRows v003 := by
  exact mul_certificate _ _ _ _ _ (matrix_w223 hA hB) (matrix_w001 hA hB) product000

theorem matrix_w225 : toMatrix (w225 (a hA) (b hB)) = decodeRows v004 := by
  exact mul_certificate _ _ _ _ _ (matrix_w224 hA hB) (matrix_w001 hA hB) product001

theorem matrix_w226 : toMatrix (w226 (a hA) (b hB)) = decodeRows v224 := by
  exact mul_certificate _ _ _ _ _ (matrix_w225 hA hB) (matrix_w001 hA hB) product243

theorem matrix_w227 : toMatrix (w227 (a hA) (b hB)) = decodeRows v001 := by
  exact mul_certificate _ _ _ _ _ (matrix_w226 hA hB) (matrix_w001 hA hB) product246

theorem matrix_w228 : toMatrix (w228 (a hA) (b hB)) = decodeRows v000 := by
  exact mul_certificate _ _ _ _ _ (matrix_w227 hA hB) (matrix_w000 hA hB) product156

theorem matrix_w229 : toMatrix (w229 (a hA) (b hB)) = decodeRows v002 := by
  exact mul_certificate _ _ _ _ _ (matrix_w228 hA hB) (matrix_w001 hA hB) product157

theorem matrix_w230 : toMatrix (w230 (a hA) (b hB)) = decodeRows v226 := by
  exact mul_certificate _ _ _ _ _ (matrix_w229 hA hB) (matrix_w001 hA hB) product247

theorem matrix_w231 : toMatrix (w231 (a hA) (b hB)) = decodeRows v227 := by
  exact mul_certificate _ _ _ _ _ (matrix_w230 hA hB) (matrix_w001 hA hB) product248

theorem matrix_w232 : toMatrix (w232 (a hA) (b hB)) = decodeRows v228 := by
  exact mul_certificate _ _ _ _ _ (matrix_w231 hA hB) (matrix_w000 hA hB) product249

theorem matrix_w233 : toMatrix (w233 (a hA) (b hB)) = decodeRows v229 := by
  exact mul_certificate _ _ _ _ _ (matrix_w232 hA hB) (matrix_w001 hA hB) product250

theorem matrix_w234 : toMatrix (w234 (a hA) (b hB)) = decodeRows v230 := by
  exact mul_certificate _ _ _ _ _ (matrix_w233 hA hB) (matrix_w000 hA hB) product251

theorem matrix_w235 : toMatrix (w235 (a hA) (b hB)) = decodeRows v231 := by
  exact inv_certificate _ _ _ (matrix_w234 hA hB) (product252.trans decode_identity)

theorem matrix_w236 : toMatrix (w236 (a hA) (b hB)) = decodeRows v232 := by
  exact mul_certificate _ _ _ _ _ (matrix_w235 hA hB) (matrix_w154 hA hB) product253

theorem matrix_w237 : toMatrix (w237 (a hA) (b hB)) = decodeRows v233 := by
  exact mul_certificate _ _ _ _ _ (matrix_w236 hA hB) (matrix_w234 hA hB) product254

theorem matrix_w238 : toMatrix (w238 (a hA) (b hB)) = decodeRows v234 := by
  exact mul_certificate _ _ _ _ _ (matrix_w154 hA hB) (matrix_w237 hA hB) product255

theorem matrix_w239 : toMatrix (w239 (a hA) (b hB)) = decodeRows v238 := by
  rw [w239, map_pow, matrix_w238 hA hB, power234_16]

theorem matrix_w240 : toMatrix (w240 (a hA) (b hB)) = decodeRows v239 := by
  exact mul_certificate _ _ _ _ _ (matrix_w239 hA hB) (matrix_w235 hA hB) product260

theorem matrix_w241 : toMatrix (w241 (a hA) (b hB)) = decodeRows v240 := by
  exact mul_certificate _ _ _ _ _ (matrix_w214 hA hB) (matrix_w240 hA hB) product261

theorem matrix_w242 : toMatrix (w242 (a hA) (b hB)) = decodeRows v241 := by
  exact mul_certificate _ _ _ _ _ (matrix_w241 hA hB) (matrix_w185 hA hB) product262

theorem matrix_w243 : toMatrix (w243 (a hA) (b hB)) = decodeRows v242 := by
  exact mul_certificate _ _ _ _ _ (matrix_w159 hA hB) (matrix_w242 hA hB) product263

theorem matrix_w244 : toMatrix (w244 (a hA) (b hB)) = decodeRows v226 := by
  exact mul_certificate _ _ _ _ _ (matrix_w001 hA hB) (matrix_w001 hA hB) product247

theorem matrix_w245 : toMatrix (w245 (a hA) (b hB)) = decodeRows v227 := by
  exact mul_certificate _ _ _ _ _ (matrix_w244 hA hB) (matrix_w001 hA hB) product248

theorem matrix_w246 : toMatrix (w246 (a hA) (b hB)) = decodeRows v228 := by
  exact mul_certificate _ _ _ _ _ (matrix_w245 hA hB) (matrix_w000 hA hB) product249

theorem matrix_w247 : toMatrix (w247 (a hA) (b hB)) = decodeRows v229 := by
  exact mul_certificate _ _ _ _ _ (matrix_w246 hA hB) (matrix_w001 hA hB) product250

theorem matrix_w248 : toMatrix (w248 (a hA) (b hB)) = decodeRows v243 := by
  exact mul_certificate _ _ _ _ _ (matrix_w247 hA hB) (matrix_w001 hA hB) product264

theorem matrix_w249 : toMatrix (w249 (a hA) (b hB)) = decodeRows v244 := by
  exact mul_certificate _ _ _ _ _ (matrix_w248 hA hB) (matrix_w001 hA hB) product265

theorem matrix_w250 : toMatrix (w250 (a hA) (b hB)) = decodeRows v228 := by
  exact mul_certificate _ _ _ _ _ (matrix_w249 hA hB) (matrix_w001 hA hB) product266

theorem matrix_w251 : toMatrix (w251 (a hA) (b hB)) = decodeRows v229 := by
  exact mul_certificate _ _ _ _ _ (matrix_w250 hA hB) (matrix_w001 hA hB) product250

theorem matrix_w252 : toMatrix (w252 (a hA) (b hB)) = decodeRows v243 := by
  exact mul_certificate _ _ _ _ _ (matrix_w251 hA hB) (matrix_w001 hA hB) product264

theorem matrix_w253 : toMatrix (w253 (a hA) (b hB)) = decodeRows v245 := by
  exact mul_certificate _ _ _ _ _ (matrix_w252 hA hB) (matrix_w000 hA hB) product267

theorem matrix_w254 : toMatrix (w254 (a hA) (b hB)) = decodeRows v243 := by
  exact mul_certificate _ _ _ _ _ (matrix_w253 hA hB) (matrix_w000 hA hB) product268

theorem matrix_w255 : toMatrix (w255 (a hA) (b hB)) = decodeRows v245 := by
  exact mul_certificate _ _ _ _ _ (matrix_w254 hA hB) (matrix_w000 hA hB) product267

theorem matrix_w256 : toMatrix (w256 (a hA) (b hB)) = decodeRows v243 := by
  exact mul_certificate _ _ _ _ _ (matrix_w255 hA hB) (matrix_w000 hA hB) product268

theorem matrix_w257 : toMatrix (w257 (a hA) (b hB)) = decodeRows v244 := by
  exact mul_certificate _ _ _ _ _ (matrix_w256 hA hB) (matrix_w001 hA hB) product265

theorem matrix_w258 : toMatrix (w258 (a hA) (b hB)) = decodeRows v228 := by
  exact mul_certificate _ _ _ _ _ (matrix_w257 hA hB) (matrix_w001 hA hB) product266

theorem matrix_w259 : toMatrix (w259 (a hA) (b hB)) = decodeRows v229 := by
  exact mul_certificate _ _ _ _ _ (matrix_w258 hA hB) (matrix_w001 hA hB) product250

theorem matrix_w260 : toMatrix (w260 (a hA) (b hB)) = decodeRows v230 := by
  exact mul_certificate _ _ _ _ _ (matrix_w259 hA hB) (matrix_w000 hA hB) product251

theorem matrix_w261 : toMatrix (w261 (a hA) (b hB)) = decodeRows v246 := by
  exact mul_certificate _ _ _ _ _ (matrix_w260 hA hB) (matrix_w001 hA hB) product269

theorem matrix_w262 : toMatrix (w262 (a hA) (b hB)) = decodeRows v247 := by
  exact mul_certificate _ _ _ _ _ (matrix_w261 hA hB) (matrix_w000 hA hB) product270

theorem matrix_w263 : toMatrix (w263 (a hA) (b hB)) = decodeRows v246 := by
  exact mul_certificate _ _ _ _ _ (matrix_w262 hA hB) (matrix_w000 hA hB) product271

theorem matrix_w264 : toMatrix (w264 (a hA) (b hB)) = decodeRows v248 := by
  exact mul_certificate _ _ _ _ _ (matrix_w263 hA hB) (matrix_w001 hA hB) product272

theorem matrix_w265 : toMatrix (w265 (a hA) (b hB)) = decodeRows v249 := by
  exact inv_certificate _ _ _ (matrix_w264 hA hB) (product273.trans decode_identity)

theorem matrix_w266 : toMatrix (w266 (a hA) (b hB)) = decodeRows v250 := by
  exact mul_certificate _ _ _ _ _ (matrix_w265 hA hB) (matrix_w154 hA hB) product274

theorem matrix_w267 : toMatrix (w267 (a hA) (b hB)) = decodeRows v251 := by
  exact mul_certificate _ _ _ _ _ (matrix_w266 hA hB) (matrix_w264 hA hB) product275

theorem matrix_w268 : toMatrix (w268 (a hA) (b hB)) = decodeRows v252 := by
  exact mul_certificate _ _ _ _ _ (matrix_w154 hA hB) (matrix_w267 hA hB) product276

theorem matrix_w269 : toMatrix (w269 (a hA) (b hB)) = decodeRows v257 := by
  rw [w269, map_pow, matrix_w268 hA hB, power252_20]

theorem matrix_w270 : toMatrix (w270 (a hA) (b hB)) = decodeRows v258 := by
  exact mul_certificate _ _ _ _ _ (matrix_w188 hA hB) (matrix_w269 hA hB) product282

theorem matrix_w271 : toMatrix (w271 (a hA) (b hB)) = decodeRows v259 := by
  exact mul_certificate _ _ _ _ _ (matrix_w270 hA hB) (matrix_w185 hA hB) product283

theorem matrix_w272 : toMatrix (w272 (a hA) (b hB)) = decodeRows v226 := by
  exact mul_certificate _ _ _ _ _ (matrix_w129 hA hB) (matrix_w001 hA hB) product247

theorem matrix_w273 : toMatrix (w273 (a hA) (b hB)) = decodeRows v260 := by
  exact mul_certificate _ _ _ _ _ (matrix_w272 hA hB) (matrix_w000 hA hB) product284

theorem matrix_w274 : toMatrix (w274 (a hA) (b hB)) = decodeRows v261 := by
  exact mul_certificate _ _ _ _ _ (matrix_w273 hA hB) (matrix_w001 hA hB) product285

theorem matrix_w275 : toMatrix (w275 (a hA) (b hB)) = decodeRows v262 := by
  exact mul_certificate _ _ _ _ _ (matrix_w274 hA hB) (matrix_w000 hA hB) product286

theorem matrix_w276 : toMatrix (w276 (a hA) (b hB)) = decodeRows v263 := by
  exact mul_certificate _ _ _ _ _ (matrix_w275 hA hB) (matrix_w001 hA hB) product287

theorem matrix_w277 : toMatrix (w277 (a hA) (b hB)) = decodeRows v264 := by
  exact mul_certificate _ _ _ _ _ (matrix_w276 hA hB) (matrix_w001 hA hB) product288

theorem matrix_w278 : toMatrix (w278 (a hA) (b hB)) = decodeRows v265 := by
  exact mul_certificate _ _ _ _ _ (matrix_w277 hA hB) (matrix_w001 hA hB) product289

theorem matrix_w279 : toMatrix (w279 (a hA) (b hB)) = decodeRows v262 := by
  exact mul_certificate _ _ _ _ _ (matrix_w278 hA hB) (matrix_w001 hA hB) product290

theorem matrix_w280 : toMatrix (w280 (a hA) (b hB)) = decodeRows v261 := by
  exact mul_certificate _ _ _ _ _ (matrix_w279 hA hB) (matrix_w000 hA hB) product291

theorem matrix_w281 : toMatrix (w281 (a hA) (b hB)) = decodeRows v266 := by
  exact mul_certificate _ _ _ _ _ (matrix_w280 hA hB) (matrix_w001 hA hB) product292

theorem matrix_w282 : toMatrix (w282 (a hA) (b hB)) = decodeRows v267 := by
  exact mul_certificate _ _ _ _ _ (matrix_w281 hA hB) (matrix_w001 hA hB) product293

theorem matrix_w283 : toMatrix (w283 (a hA) (b hB)) = decodeRows v260 := by
  exact mul_certificate _ _ _ _ _ (matrix_w282 hA hB) (matrix_w001 hA hB) product294

theorem matrix_w284 : toMatrix (w284 (a hA) (b hB)) = decodeRows v261 := by
  exact mul_certificate _ _ _ _ _ (matrix_w283 hA hB) (matrix_w001 hA hB) product285

theorem matrix_w285 : toMatrix (w285 (a hA) (b hB)) = decodeRows v266 := by
  exact mul_certificate _ _ _ _ _ (matrix_w284 hA hB) (matrix_w001 hA hB) product292

theorem matrix_w286 : toMatrix (w286 (a hA) (b hB)) = decodeRows v267 := by
  exact mul_certificate _ _ _ _ _ (matrix_w285 hA hB) (matrix_w001 hA hB) product293

theorem matrix_w287 : toMatrix (w287 (a hA) (b hB)) = decodeRows v268 := by
  exact mul_certificate _ _ _ _ _ (matrix_w286 hA hB) (matrix_w000 hA hB) product295

theorem matrix_w288 : toMatrix (w288 (a hA) (b hB)) = decodeRows v249 := by
  exact mul_certificate _ _ _ _ _ (matrix_w287 hA hB) (matrix_w001 hA hB) product296

theorem matrix_w289 : toMatrix (w289 (a hA) (b hB)) = decodeRows v269 := by
  exact mul_certificate _ _ _ _ _ (matrix_w288 hA hB) (matrix_w001 hA hB) product297

theorem matrix_w290 : toMatrix (w290 (a hA) (b hB)) = decodeRows v270 := by
  exact mul_certificate _ _ _ _ _ (matrix_w289 hA hB) (matrix_w000 hA hB) product298

theorem matrix_w291 : toMatrix (w291 (a hA) (b hB)) = decodeRows v271 := by
  exact inv_certificate _ _ _ (matrix_w290 hA hB) (product299.trans decode_identity)

theorem matrix_w292 : toMatrix (w292 (a hA) (b hB)) = decodeRows v272 := by
  exact mul_certificate _ _ _ _ _ (matrix_w291 hA hB) (matrix_w154 hA hB) product300

theorem matrix_w293 : toMatrix (w293 (a hA) (b hB)) = decodeRows v273 := by
  exact mul_certificate _ _ _ _ _ (matrix_w292 hA hB) (matrix_w290 hA hB) product301

theorem matrix_w294 : toMatrix (w294 (a hA) (b hB)) = decodeRows v274 := by
  exact mul_certificate _ _ _ _ _ (matrix_w154 hA hB) (matrix_w293 hA hB) product302

theorem matrix_w295 : toMatrix (w295 (a hA) (b hB)) = decodeRows v278 := by
  rw [w295, map_pow, matrix_w294 hA hB, power274_12]

theorem matrix_w296 : toMatrix (w296 (a hA) (b hB)) = decodeRows v279 := by
  exact mul_certificate _ _ _ _ _ (matrix_w271 hA hB) (matrix_w295 hA hB) product307

theorem matrix_w297 : toMatrix (w297 (a hA) (b hB)) = decodeRows v280 := by
  exact inv_certificate _ _ _ (matrix_w296 hA hB) (product308.trans decode_identity)

theorem matrix_w298 : toMatrix (w298 (a hA) (b hB)) = decodeRows v281 := by
  exact mul_certificate _ _ _ _ _ (matrix_w243 hA hB) (matrix_w297 hA hB) product309

theorem matrix_w299 : toMatrix (w299 (a hA) (b hB)) = decodeRows v282 := by
  exact mul_certificate _ _ _ _ _ (matrix_w298 hA hB) (matrix_w039 hA hB) product310

theorem matrix_w300 : toMatrix (w300 (a hA) (b hB)) = decodeRows v283 := by
  exact inv_certificate _ _ _ (matrix_w298 hA hB) (product311.trans decode_identity)

theorem matrix_w301 : toMatrix (w301 (a hA) (b hB)) = decodeRows v146 := by
  exact mul_certificate _ _ _ _ _ (matrix_w299 hA hB) (matrix_w300 hA hB) product312

theorem checked_z : w055 (a hA) (b hB) = w108 (a hA) (b hB) :=
  toMatrix_injective ((matrix_w055 hA hB).trans (matrix_w108 hA hB).symm)

theorem checked_x : w126 (a hA) (b hB) = w301 (a hA) (b hB) :=
  toMatrix_injective ((matrix_w126 hA hB).trans (matrix_w301 hA hB).symm)


end Janko4.Simplicity.Elevens.BridgeCertificate
