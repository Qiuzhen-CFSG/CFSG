module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair.SecondOrbits.TableSupport

/-!
# A nonabelian three-subgroup in the degree-100 J₂ carrier

Two words in the original ATLAS generators admit 27 distinct normal forms,
closed under generator multiplication. This file checks the finite permutation
identities; `ThreeSylow` turns them into a Sylow subgroup and an odd-rank bound.
All tables are compared with the original carrier generators by the kernel.

Source: ATLAS `J2G1-p100B0` (original data and attribution in
`Theory/SpecificGroups/LeechRelated/AtlasCarriers/source/`); the order and
three-local context are GLS3, Table 5.3g. The certificate was discovered by
word enumeration; the discovery computation is not a proof input.
-/

@[expose] public section
namespace CFSG.Quasithin.MainConverse.SporadicLocal.J2Rank
open Subgroup Theory.GroupTheory
open Sporadic.LeechRelated.J2 Sporadic.LeechRelated.J2.GeneratorPair
open Sporadic.LeechRelated.J2.GeneratorPair.SecondOrbitCertificate
set_option maxRecDepth 100000

def xWord : List (Fin 3) := [0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0]
def yWord : List (Fin 3) := [1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2]
def x : Carrier := evalWord ![a,b,b⁻¹] xWord
def y : Carrier := evalWord ![a,b,b⁻¹] yWord
def xMap := packedMap 2475446676703423832909981399859469181581741148032220012819066410901403736590119923000355006587749973909727632624427794457525144893477864230855952424232563017032531388649211936371243781402992136675954335025252876
def xInvMap := packedMap 2732648375453525417472475026912553115381707082328427585109153368414871909480697794563251608417458824078783085639464709468317506883497766269769739278560908117659341688735768973592629152158106330079259795683433792
def yMap := packedMap 1735729703519851601881862923511609011817253503716862098193596889357718824867204263913386559228847095756847317176502799736002841658494490747807646710938792459320441387395813810888047078097384596178491430662431241
def yInvMap := packedMap 766826111562333537705958933755543276648160862978279036520454356725857075104064657306582523806831531174461475042151528674407551119700754415461535568926905519731240278613826422585770083964882798367694524691178954
def fastX : Equiv.Perm (Fin 100) := tablePerm xMap xInvMap
  (by decide +kernel) (by decide +kernel)
def fastY : Equiv.Perm (Fin 100) := tablePerm yMap yInvMap
  (by decide +kernel) (by decide +kernel)

theorem x_fast : inclusion x = fastX := by
  change evalWord ![generatorA, generatorB, generatorB⁻¹] xWord = fastX
  rw [generatorA_eq_table, generatorB_eq_table]
  decide +kernel

theorem y_fast : inclusion y = fastY := by
  change evalWord ![generatorA, generatorB, generatorB⁻¹] yWord = fastY
  rw [generatorA_eq_table, generatorB_eq_table]
  decide +kernel

def generators : Fin 2 → Carrier := ![x,y]
def P : Subgroup Carrier := Subgroup.closure (Set.range generators)
def nfWords : Fin 27 → List (Fin 4) := ![[], [0], [1], [2], [3], [0, 1], [0, 3], [1, 0], [1, 2], [2, 1], [2, 3], [3, 0], [3, 2], [0, 1, 0], [0, 1, 2], [0, 3, 0], [0, 3, 2], [1, 0, 1], [1, 0, 3], [1, 2, 3], [2, 1, 0], [2, 1, 2], [2, 3, 0], [3, 0, 1], [3, 2, 1], [0, 1, 2, 3], [0, 3, 2, 1]]
def signedGen : Fin 4 → Carrier := ![x, y, x⁻¹, y⁻¹]
def fastSignedGen : Fin 4 → Equiv.Perm (Fin 100) := ![fastX, fastY, fastX⁻¹, fastY⁻¹]
def reps : Fin 27 → Carrier := fun i => evalWord signedGen (nfWords i)
def fastReps : Fin 27 → Equiv.Perm (Fin 100) := fun i => evalWord fastSignedGen (nfWords i)
def next : Fin 27 → Fin 2 → Fin 27 := ![![1, 2], ![3, 5], ![7, 4], ![0, 9], ![11, 0], ![13, 6], ![15, 1], ![8, 17], ![2, 15], ![20, 10], ![22, 3], ![12, 23], ![4, 24], ![14, 12], ![5, 22], ![16, 19], ![6, 26], ![10, 18], ![24, 7], ![25, 8], ![21, 16], ![9, 11], ![17, 25], ![19, 21], ![26, 13], ![23, 14], ![18, 20]]
def prev : Fin 27 → Fin 2 → Fin 27 := ![![3, 4], ![0, 6], ![8, 0], ![1, 10], ![12, 2], ![14, 1], ![16, 5], ![2, 18], ![7, 19], ![21, 3], ![17, 9], ![4, 21], ![11, 13], ![5, 24], ![13, 25], ![6, 8], ![15, 20], ![22, 7], ![26, 17], ![23, 15], ![9, 26], ![20, 23], ![10, 14], ![25, 11], ![18, 12], ![19, 22], ![24, 16]]

theorem fast_transitions : ∀ i j, fastReps i * (![fastX,fastY] : Fin 2 → _) j = fastReps (next i j) := by
  apply allFin
  decide +kernel

theorem index_inverse : ∀ i j, next (prev i j) j = i := by decide +kernel

def point : Fin 27 → Fin 100 := ![0, 12, 9, 64, 74, 80, 68, 11, 20, 83, 53, 21, 44, 82, 58, 93, 35, 81, 75, 69, 94, 1, 40, 88, 8, 61, 71]
theorem fast_point : ∀ i, fastReps i 0 = point i := by
  apply allFin
  decide +kernel

theorem point_injective : Function.Injective point := by decide +kernel

theorem fast_noncommute : fastX * fastY ≠ fastY * fastX := by decide +kernel

end CFSG.Quasithin.MainConverse.SporadicLocal.J2Rank
