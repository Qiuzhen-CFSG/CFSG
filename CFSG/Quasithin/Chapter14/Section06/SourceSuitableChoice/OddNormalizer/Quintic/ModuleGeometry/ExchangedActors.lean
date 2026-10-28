module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.ModuleGeometry.ExchangedTorus

/-!
# The exchanged Borel quotients in the original actor group

The proved Sylow-core containment gives Kᵢ ∩ O₂(H) = Kᵢ ∩ T. Together
with the computed core of Kᵢ ∩ H, this identifies the kernel of the
literal map Kᵢ ∩ H → H/O₂(H). The resulting quotient isomorphism has
image exactly actorImage H Kᵢ, and its evaluation formula retains that
original quotient map. Both actual component actor images have order
dividing five by the Borel torus calculation.

The final theorem constructs these constraints from Context and the
checked residual exclusion. They supply the component-actor constraints
for the remaining identification with the original 14.6.12 factors.
That support alignment, the opposite-support centralizations and the
conjugated point-centralizer identity still belong to
qt-e-14615-quintic-exclusion, together with final p=3 assembly.
The allowed earlier 14.6.12--14 inputs, including the factor-join index
owned by qt-e-14612-singleton, remain unchanged and require their original
source owners' discharge in the suitable-choice assembly.
Source: Aschbacher--Smith 14.6.15, printed pp.1033--1034.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic.ModuleGeometry
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ComponentExclusion
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc H H0 H1 H2 : Subgroup G}
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    {a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T)}
    (s : Context T M Mc H H0 H1 H2 a)
    (b : ExchangedFactorData (T : Subgroup G) Mc H (centralInvolutions T))

include s b in
/-- The original H-core meets each subgroup of K_z in its prescribed Sylow intersection. -/
theorem source_exchanged_component_core_intersection {K : Subgroup G}
    (hKz : K ≤ residualClosure H Mc) :
    K ⊓ H.pCoreIn 2 = K ⊓ (T : Subgroup G) := by
  have hQT : H.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := H.pCoreIn_le_sylow (T.subtype s.outside.1.2)
    change H.pCoreIn 2 ≤ ((T : Subgroup G).subgroupOf H).map H.subtype at hh
    rwa [map_subgroupOf_eq_of_le s.outside.1.2] at hh
  exact le_antisymm (inf_le_inf_left _ hQT)
    (le_inf inf_le_left ((le_inf inf_le_right (inf_le_left.trans hKz)).trans
      (source_exchanged_closure_sylow_le_core s b)))

include s b in
/-- Identify the intrinsic intersection quotient with the literal actor image, including its quotient map. -/
theorem source_exchanged_component_actor_quotient {K : Subgroup G}
    (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    (em : Nonempty ((K ⧸ pCore 2 K) ≃* Theory.PSL2.SixteenWreathComponents.L))
    (hKz : K ≤ residualClosure H Mc) :
    ∃ e : ((K ⊓ H : Subgroup G) ⧸ pCore 2 (K ⊓ H : Subgroup G)) ≃* actorImage H K,
      ∀ x : (K ⊓ H : Subgroup G),
        (e (QuotientGroup.mk' (pCore 2 (K ⊓ H : Subgroup G)) x) : H ⧸ pCore 2 H) =
          QuotientGroup.mk' (pCore 2 H) ⟨x,x.property.2⟩ := by
  let B := K ⊓ H
  let q := QuotientGroup.mk' (pCore 2 H)
  let f0 : B →* H ⧸ pCore 2 H := q.comp (inclusion (show B ≤ H from inf_le_right))
  let f : B →* actorImage H K := f0.codRestrict _
    (fun x => mem_map_of_mem q x.property.1)
  have hf : Function.Surjective f := by
    rintro ⟨x,hx⟩
    obtain ⟨y,hy,rfl⟩ := hx
    exact ⟨⟨y,hy,y.property⟩,rfl⟩
  have hc := source_exchanged_component_intersection_core s hKM hK em
  have hi := source_exchanged_component_core_intersection s b hKz
  have hk : f.ker = pCore 2 B := by
    ext x
    have hx : x ∈ pCore 2 B ↔ (x : G) ∈ K ⊓ (T : Subgroup G) := by
      rw [←hc]
      exact (mem_map_iff_mem B.subtype_injective).symm
    have hq : q ⟨(x : G),x.property.2⟩ = 1 ↔ (x : G) ∈ H.pCoreIn 2 := by
      exact (QuotientGroup.eq_one_iff (N := pCore 2 H) ⟨(x : G),x.property.2⟩).trans
        (mem_map_iff_mem H.subtype_injective).symm
    change f x = 1 ↔ x ∈ pCore 2 B
    rw [hx,←hi]
    constructor
    · intro he
      exact ⟨x.property.1,hq.mp (congrArg Subtype.val he)⟩
    · intro he
      exact Subtype.ext (hq.mpr he.2)
  let e := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)
  exact ⟨e,fun x => rfl⟩

include s b in
/-- The torus restriction applies to the original image in H/O₂(H). -/
theorem source_exchanged_component_actor_card_dvd_five {K : Subgroup G}
    (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    (em : Nonempty ((K ⧸ pCore 2 K) ≃* Theory.PSL2.SixteenWreathComponents.L))
    (hKz : K ≤ residualClosure H Mc) : Nat.card (actorImage H K) ∣ 5 := by
  obtain ⟨e,_⟩ := source_exchanged_component_actor_quotient s b hKM hK em hKz
  rw [←Nat.card_congr e.toEquiv]
  exact source_exchanged_intersection_quotient_card_dvd_five s hKM hK em

include s in
/-- Construct the two actual component actor constraints from the unchanged source context. -/
theorem source_exchanged_actor_orders :
    ∃ b : ExchangedFactorData (T : Subgroup G) Mc H (centralInvolutions T),
      Nat.card (actorImage H b.K1) ∣ 5 ∧ Nat.card (actorImage H b.K2) ∣ 5 ∧
      b.K1 ⊓ H.pCoreIn 2 = b.K1 ⊓ (T : Subgroup G) ∧
      b.K2 ⊓ H.pCoreIn 2 = b.K2 ⊓ (T : Subgroup G) := by
  obtain ⟨b⟩ := source_exchanged_factor_data s
  have h1 : b.K1 ≤ residualClosure H Mc :=
    (le_sup_left : b.K1 ≤ b.K1 ⊔ b.K2).trans_eq b.join_eq
  have h2 : b.K2 ≤ residualClosure H Mc :=
    (le_sup_right : b.K2 ≤ b.K1 ⊔ b.K2).trans_eq b.join_eq
  exact ⟨b,source_exchanged_component_actor_card_dvd_five s b b.first_le b.first_component b.first_model h1,
    source_exchanged_component_actor_card_dvd_five s b b.second_le b.second_component b.second_model h2,
    source_exchanged_component_core_intersection s b h1,
    source_exchanged_component_core_intersection s b h2⟩

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic.ModuleGeometry
