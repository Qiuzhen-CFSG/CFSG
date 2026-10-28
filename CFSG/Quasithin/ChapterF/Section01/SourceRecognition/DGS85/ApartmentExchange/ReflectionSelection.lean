module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.SourcePathRoots
public import Theory.GroupTheory.WeakBNPair.RegularTree.CartanReflection

/-!
# Reflection selection in the marked universal endpoints

Use the actual quotient of each original universal endpoint by its intrinsic
two-core. A quotient reflection normalizing the whole source Cartan lifts
through the two-kernel by Hall conjugacy. In the branch where the Cartan
centralizer in that kernel is trivial, the corrected lift is an involution.
Its quotient image remains outside the image of the entire original Borel,
so it fixes its marked endpoint and moves the other one.

Both selected reflections feed the existing construction of the actual
long-path radicals. This discharges its four reflection premises from the
stated quotient data. Existence of that quotient data, the cases with a
nontrivial kernel centralizer, prescribed local-actor conjugacy, and the
remaining Chapter 14 exchange and quotient root-sign arguments are not
asserted here. The natural-module source extension treats a more precise
root-conjugacy choice separately.

Source: DGS, *Groups and Graphs* (1985), (14.2), pp.210--211; the actual
universal amalgam convention of (14.0), p.208.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.WeakBNPair.RegularTree Subgroup.CosetGeometry
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.SuzukiContainment
open CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
namespace CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
namespace ReducedCartan
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The original universal endpoint, retaining its Boolean marking. -/
abbrev reflectionEndpoint (L : Fin 2 → Subgroup G) (S : Subgroup G) (i : Bool) :=
  Universal.cosetFamily (reducedAmalgam L S) i

/-- The actual quotient of the marked endpoint by its intrinsic two-core. -/
abbrev reflectionQuotient (L : Fin 2 → Subgroup G) (S : Subgroup G) (i : Bool) :=
  reflectionEndpoint L S i ⧸ pCore 2 (reflectionEndpoint L S i)

/-- The quotient map is the original endpoint quotient, before constructing a reflection. -/
def reflectionQuotientMap (L : Fin 2 → Subgroup G) (S : Subgroup G) (i : Bool) :
    reflectionEndpoint L S i →* reflectionQuotient L S i :=
  QuotientGroup.mk' (pCore 2 (reflectionEndpoint L S i))

private theorem middle_le_reflectionEndpoint (i : Bool) :
    originalMiddle (reducedAmalgam L S) ≤ reflectionEndpoint L S i := by
  rw [originalMiddle,←Universal.overlap_eq _
    (inclusion_injective (commonBorel_le_parabolic 0))
    (inclusion_injective (commonBorel_le_parabolic 1))]
  cases i
  · exact inf_le_left
  · exact inf_le_right

/-- The same whole source Cartan inside the marked endpoint. -/
def reflectionCartan (c : CompatibleCartans L (reducedSylow L S)) (i : Bool) :
    Subgroup (reflectionEndpoint L S i) := (cartan c).subgroupOf _

/-- Earlier local data for the fixed-point-free Cartan branch of (14.2).
Only a quotient reflection is supplied; the actual involution is constructed. -/
structure QuotientReflectionInput (c : CompatibleCartans L (reducedSylow L S)) (i : Bool) where
  weyl : reflectionQuotient L S i
  square : weyl*weyl=1
  outside : weyl ∉ ((originalMiddle (reducedAmalgam L S)).subgroupOf
    (reflectionEndpoint L S i)).map (reflectionQuotientMap L S i)
  normalizes : weyl∈normalizer ((reflectionCartan c i).map
    (reflectionQuotientMap L S i) : Set (reflectionQuotient L S i))
  centralizer : pCore 2 (reflectionEndpoint L S i) ⊓
    centralizer (reflectionCartan c i : Set (reflectionEndpoint L S i))=⊥

variable (h : HypothesisF11 L S) (c : CompatibleCartans L (reducedSylow L S))

include h in
/-- The local quotient data yield an actual endpoint involution in the
normalizer of the full original Cartan and outside the full original Borel. -/
theorem exists_reflection_of_quotient (i : Bool) (d : QuotientReflectionInput c i) :
    ∃ t : reflectionEndpoint L S i,
      (t : (reducedAmalgam L S).Universal)∈normalizer (cartan c : Set _) ∧
      t*t=1 ∧ orderOf t=2 ∧ reflectionQuotientMap L S i t=d.weyl ∧
      (t : (reducedAmalgam L S).Universal)∉originalMiddle (reducedAmalgam L S) := by
  let P := reflectionEndpoint L S i
  let π := reflectionQuotientMap L S i
  let K := (cartan c).subgroupOf P
  let := (reduced_hypothesis h).finite_parabolic 0
  let := (reduced_hypothesis h).finite_parabolic 1
  let : Finite P := by
    change Finite (Universal.cosetFamily (reducedAmalgam L S) i)
    rw [←stabilizer_base (Universal.cosetFamily (reducedAmalgam L S)) i]
    exact source_vertexStabilizer_finite _ _
  have hKP : cartan c ≤ P := (cartan_le c).trans (middle_le_reflectionEndpoint i)
  have hodd : Nat.Coprime 2 (Nat.card K) := by
    change Nat.Coprime 2 (Nat.card ((cartan c).subgroupOf P))
    rw [Nat.card_congr (subgroupOfEquivOfLe hKP).toEquiv]
    exact cartan_odd c
  let := cartan_abelian h c
  let : IsMulCommutative K := IsMulCommutative.of_comm fun x y =>
    (subgroupOfEquivOfLe hKP).injective (by simp only [map_mul]; exact mul_comm' _ _)
  let : Group.IsSolvable K := Group.isSolvable_of_comm (mul_comm' (M := K))
  have hker : π.ker=pCore 2 P := QuotientGroup.ker_mk' _
  have hQ : IsPGroup 2 π.ker := hker.symm ▸ pCore_isPGroup
  have hC : π.ker ⊓ centralizer (K : Set P)=⊥ := by rw [hker]; exact d.centralizer
  obtain ⟨g,hg⟩ := QuotientGroup.mk'_surjective (pCore 2 P) d.weyl
  change π g=d.weyl at hg
  have hgne : π g≠1 := by
    rw [hg]
    intro he
    exact d.outside (he ▸ Subgroup.one_mem _)
  obtain ⟨t,ht,hsq,ho,hπt,_⟩ := exists_cartan_reflection π K hQ hodd hC g
    (by rw [hg]; exact d.square) hgne (by rw [hg]; exact d.normalizes)
  refine ⟨t,?_,hsq,ho,hπt.trans hg,?_⟩
  · have hh := K.le_normalizer_map P.subtype (mem_map_of_mem P.subtype ht)
    have heK : K.map P.subtype=cartan c := map_subgroupOf_eq_of_le hKP
    rwa [heK] at hh
  · intro htB
    apply d.outside
    exact ⟨t,htB,hπt.trans hg⟩

variable (d : ∀ i : Bool, QuotientReflectionInput c i)

/-- Choose both actual local reflections using the literal quotient inputs. -/
def quotientReflections (i : Bool) : (reducedAmalgam L S).Universal :=
  (Classical.choose (exists_reflection_of_quotient h c i (d i)) : reflectionEndpoint L S i)

/-- Both chosen reflections fix their matching original endpoint. -/
theorem quotientReflections_fix (i : Bool) :
    quotientReflections h c d i • base (Universal.cosetFamily (reducedAmalgam L S)) i =
      base (Universal.cosetFamily (reducedAmalgam L S)) i := by
  have ht := (Classical.choose (exists_reflection_of_quotient h c i (d i))).property
  change quotientReflections h c d i∈Universal.cosetFamily (reducedAmalgam L S) i at ht
  rwa [←stabilizer_base (Universal.cosetFamily (reducedAmalgam L S)) i] at ht

/-- Neither chosen reflection fixes the other original endpoint. -/
theorem quotientReflections_move (i : Bool) :
    quotientReflections h c d i • base (Universal.cosetFamily (reducedAmalgam L S)) (!i) ≠
      base (Universal.cosetFamily (reducedAmalgam L S)) (!i) := by
  intro he
  have ht := (Classical.choose (exists_reflection_of_quotient h c i (d i))).property
  have hu : quotientReflections h c d i∈reflectionEndpoint L S (!i) := by
    change quotientReflections h c d i∈Universal.cosetFamily (reducedAmalgam L S) (!i)
    rw [←stabilizer_base (Universal.cosetFamily (reducedAmalgam L S)) (!i)]
    exact he
  have hnot : quotientReflections h c d i∉originalMiddle (reducedAmalgam L S) :=
    (Classical.choose_spec (exists_reflection_of_quotient h c i (d i))).2.2.2.2
  apply hnot
  rw [originalMiddle,←Universal.overlap_eq _
    (inclusion_injective (commonBorel_le_parabolic 0))
    (inclusion_injective (commonBorel_le_parabolic 1))]
  cases i
  · exact ⟨ht,hu⟩
  · exact ⟨hu,ht⟩

/-- The constructed lifts are actual involutions in the universal completion. -/
theorem quotientReflections_square (i : Bool) :
    quotientReflections h c d i * quotientReflections h c d i=1 :=
  congrArg Subtype.val (Classical.choose_spec (exists_reflection_of_quotient h c i (d i))).2.1

/-- The constructed lifts normalize the whole original Cartan. -/
theorem quotientReflections_normalize (i : Bool) :
    quotientReflections h c d i∈normalizer (cartan c : Set (reducedAmalgam L S).Universal) :=
  (Classical.choose_spec (exists_reflection_of_quotient h c i (d i))).1

/-- Their original local quotient images retain the prescribed Weyl elements. -/
theorem quotientReflections_image (i : Bool) :
    reflectionQuotientMap L S i
      (Classical.choose (exists_reflection_of_quotient h c i (d i)))=(d i).weyl :=
  (Classical.choose_spec (exists_reflection_of_quotient h c i (d i))).2.2.2.1

variable (n : ℕ) (hn : 1<n)
variable (htrans : BasedPathTransitive (X := (reducedAmalgam L S).Universal)
  (sourceGraph (reducedAmalgam L S)) (n+1))
variable (hthick : ∀ i, ∃ z, (sourceGraph (reducedAmalgam L S)).Adj
  (base (Universal.cosetFamily (reducedAmalgam L S)) i) z ∧
  z ≠ base (Universal.cosetFamily (reducedAmalgam L S)) (!i) ∧
  z ≠ quotientReflections h c d i • base (Universal.cosetFamily (reducedAmalgam L S)) (!i))

/-- Literal application to the existing source path-root construction.
All four reflection hypotheses are now discharged by the lifting proof. -/
def quotientReflectionPathRoots : Bool →
    LocalRootAction (X := (reducedAmalgam L S).Universal) (sourceGraph (reducedAmalgam L S)) :=
  pathRoots h c n hn (quotientReflections h c d)
    (quotientReflections_fix h c d) (quotientReflections_move h c d)
    (quotientReflections_square h c d) (quotientReflections_normalize h c d) htrans hthick

end ReducedCartan
end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
