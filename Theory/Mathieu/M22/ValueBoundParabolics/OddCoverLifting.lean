module

public import Theory.Mathieu.M22.ValueBoundParabolics.OddCoverLifting.CanonicalComplement
public import Theory.Mathieu.M22.ValueBoundParabolics.OddCoverLifting.SymmetricSplitting
public import Theory.Mathieu.M22.ValueBoundParabolics.OddCoverLifting.TwoCoreReduction

/-!
# Assembling local lifts through an odd central kernel

Restrict the cover to each inner inverse image, take its characteristic
complement, and adjoin the original Sylow subgroup. The resulting lifts map
isomorphically onto the quotient overgroups, hence have the same intrinsic
two-core quotients. Perfectness of L then gives generation of G.

The odd central splitting theorems for S₅ and S₃, followed by reduction across
the normal two-core, discharge the local splitting inputs. The final theorem
requires only the quotient pair and the stated cover hypotheses. In particular,
the kernel need only centralize L; outer automorphisms may act on it.

Source: Aschbacher–Smith, E.4.3(2), printed pp. 241–242, combined manuscript
of 1 March 2004.
-/

public section
namespace Sporadic.Mathieu.M22ValueBound.OddCoverLifting
open Subgroup
universe u

/-- Transport through the actual intrinsic two-cores. -/
noncomputable def pCoreQuotientEquiv {E F : Type*} [Group E] [Group F] (e : E ≃* F) :
    (E ⧸ pCore 2 E) ≃* (F ⧸ pCore 2 F) :=
  QuotientGroup.congr _ _ e (pCore_map_iso 2 e)

/-- Given local central splitting, construct a kernel-free lift of one quotient
overgroup, retaining the specified T and an actual group isomorphism. -/
theorem exists_local_lift {G : Type u} [Group G] [Finite G]
    (L C : Subgroup G) [L.Normal] [C.Normal]
    (hCL : C ≤ L) (hc : C ≤ centralizer (L : Set G)) (hodd : Odd (Nat.card C))
    (T : Sylow 2 G) (hgen : L ⊔ (T : Subgroup G) = ⊤)
    (P : Subgroup (G ⧸ C))
    (hTP : (T.mapSurjective (QuotientGroup.mk'_surjective C) : Subgroup (G ⧸ C)) ≤ P)
    {n : ℕ} (hsplit : OddCentralSplitting.{u} n)
    (e : ((P ⊓ L.map (QuotientGroup.mk' C) : Subgroup (G ⧸ C)) ⧸
      pCore 2 (P ⊓ L.map (QuotientGroup.mk' C) : Subgroup (G ⧸ C))) ≃*
        Equiv.Perm (Fin n)) :
    ∃ H : Subgroup G, (T : Subgroup G) ≤ H ∧
      H.map (QuotientGroup.mk' C) = P ∧ Nonempty (H ≃* P) := by
  let q := QuotientGroup.mk' C
  let A := P.comap q
  have hTA : (T : Subgroup G) ≤ A := fun x hx => hTP (mem_map_of_mem q hx)
  have hCA : C ≤ A := by
    intro x hx
    change q x ∈ P
    rw [show q x = 1 from (QuotientGroup.eq_one_iff x).mpr hx]
    exact P.one_mem
  let E := L.subgroupOf A
  let Z := C.subgroupOf A
  have hZE : Z ≤ E := fun x hx => hCL hx
  let F := P ⊓ L.map q
  let f : E →* F :=
    ((q.comp A.subtype).comp E.subtype).codRestrict F (by
      intro x
      exact ⟨x.val.property, mem_map_of_mem q x.property⟩)
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨l, hl, hly⟩ := mem_map.mp y.property.2
    have hlA : l ∈ A := by change q l ∈ P; rw [hly]; exact y.property.1
    exact ⟨⟨⟨l, hlA⟩, hl⟩, Subtype.ext hly⟩
  have hker : f.ker = Z.subgroupOf E := by
    ext x
    change (f x = 1) ↔ (x.val.val ∈ C)
    rw [← QuotientGroup.eq_one_iff]
    exact Subtype.ext_iff
  have hkC : f.ker ≤ center E := by
    rw [hker]
    intro x hx
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    apply Subtype.ext
    exact (hc hx) y.val.val y.property
  have hoddZ : Odd (Nat.card Z) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hCA).toEquiv]
    exact hodd
  have hoddK : Odd (Nat.card f.ker) := by
    rw [hker, Nat.card_congr (subgroupOfEquivOfLe hZE).toEquiv]
    exact hoddZ
  obtain ⟨D, hchar, hD⟩ := hsplit E F f hf hkC hoddK e
  let := hchar
  have hET : E ⊔ (T.subtype hTA : Subgroup A) = ⊤ := by
    apply top_unique
    intro x _
    have hx : (x : G) ∈ L ⊔ (T : Subgroup G) := hgen ▸ mem_top _
    obtain ⟨l, hl, t, ht, hlt⟩ := mem_sup_of_normal_left.mp hx
    have hlA : l ∈ A := by
      have hltA : l * t ∈ A := hlt ▸ x.property
      exact (A.mul_mem_cancel_right (hTA ht)).mp hltA
    have hh : (⟨l, hlA⟩ : A) * ⟨t, hTA ht⟩ = x := Subtype.ext hlt
    rw [← hh]
    exact mul_mem_sup hl ht
  obtain ⟨K, hTK, hK⟩ := exists_complement_containing_sylow E Z hZE hoddZ
    (T.subtype hTA) hET D (hker ▸ hD)
  let H := K.map A.subtype
  have hTH : (T : Subgroup G) ≤ H := by
    intro t ht
    exact mem_map.mpr ⟨⟨t, hTA ht⟩, hTK ht, rfl⟩
  have hCH : C ⊔ H = A := by
    have hh := congrArg (Subgroup.map A.subtype) hK.sup_eq_top
    simpa only [Z, Subgroup.map_sup, map_subgroupOf_eq_of_le hCA, ← MonoidHom.range_eq_map, range_subtype] using hh
  have hdis : Disjoint C H := by
    have hh := Subgroup.disjoint_map A.subtype_injective hK.disjoint
    simpa only [Z, map_subgroupOf_eq_of_le hCA] using hh
  have hHP : H.map q = P := by
    have hh := congrArg (Subgroup.map q) hCH
    simpa only [Subgroup.map_sup, (C.map_eq_bot_iff (f := q)).mpr (by simp [q]), bot_sup_eq,
      A, q, map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective C)] using hh
  have hi : Function.Injective (q.subgroupMap H) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    apply Subtype.ext
    exact hdis.le_bot ⟨(QuotientGroup.eq_one_iff x.val).mp
      (congrArg Subtype.val hx), x.property⟩
  exact ⟨H, hTH, hHP, ⟨(MulEquiv.ofBijective (q.subgroupMap H)
    ⟨hi, q.subgroupMap_surjective H⟩).trans (MulEquiv.subgroupCongr hHP)⟩⟩

/-- Conditional assembly of the two local lifts with specified splitting
theorems. The final cover theorem below supplies both splitting premises. -/
theorem parabolicPair_of_oddCentralSplitting {G : Type u} [Group G] [Finite G]
    (hsplit5 : OddCentralSplitting.{u} 5) (hsplit3 : OddCentralSplitting.{u} 3)
    (L C : Subgroup G) [L.Normal] [C.Normal] [Group.IsPerfect L]
    (hCL : C ≤ L) (hc : C ≤ centralizer (L : Set G)) (hodd : Odd (Nat.card C))
    (T : Sylow 2 G) (hgen : L ⊔ (T : Subgroup G) = ⊤)
    (d : Sporadic.Mathieu.M22ValueBound.InnerCompatiblePair
      (T.mapSurjective (QuotientGroup.mk'_surjective C)) (L.map (QuotientGroup.mk' C))) :
    Nonempty (Sporadic.Mathieu.M22ValueBound.ParabolicPair T) := by
  obtain ⟨H₁, hT₁, hm₁, ⟨e₁⟩⟩ := exists_local_lift L C hCL hc hodd T hgen
    d.first d.sylow_le_first hsplit5 d.firstInnerQuotient
  obtain ⟨H₂, hT₂, hm₂, ⟨e₂⟩⟩ := exists_local_lift L C hCL hc hodd T hgen
    d.second d.sylow_le_second hsplit3 d.secondInnerQuotient
  refine ⟨⟨H₁, H₂, hT₁, hT₂, ?_, (pCoreQuotientEquiv e₁).trans d.firstQuotient,
    (pCoreQuotientEquiv e₂).trans d.secondQuotient⟩⟩
  apply Sporadic.Mathieu.M22ValueBound.eq_top_of_quotient_image L C _ hCL hc
  rw [Subgroup.map_sup, hm₁, hm₂, d.generate]

/-- Odd central extensions of groups with intrinsic two-core quotient S₃
have a characteristic complement to their kernel. -/
theorem oddCentralSplitting_three : OddCentralSplitting.{u} 3 :=
  oddCentralSplitting_of_symmetricOddCentralSplitting symmetricOddCentralSplitting_three

/-- Odd central extensions of groups with intrinsic two-core quotient S₅
have a characteristic complement to their kernel. -/
theorem oddCentralSplitting_five : OddCentralSplitting.{u} 5 :=
  oddCentralSplitting_of_symmetricOddCentralSplitting symmetricOddCentralSplitting_five

/-- Lift an inner-compatible quotient pair through an odd normal kernel
central in the perfect normal subgroup L. The resulting subgroups contain
the specified T, generate G, and have intrinsic two-core quotients S₅ and S₃.
All local splitting premises are discharged by the odd central extension
theorems, so the ambient cover may be nonsplit. -/
theorem parabolicPair_of_oddCentralKernel {G : Type u} [Group G] [Finite G]
    (L C : Subgroup G) [L.Normal] [C.Normal] [Group.IsPerfect L]
    (hCL : C ≤ L) (hc : C ≤ centralizer (L : Set G)) (hodd : Odd (Nat.card C))
    (T : Sylow 2 G) (hgen : L ⊔ (T : Subgroup G) = ⊤)
    (d : Sporadic.Mathieu.M22ValueBound.InnerCompatiblePair
      (T.mapSurjective (QuotientGroup.mk'_surjective C)) (L.map (QuotientGroup.mk' C))) :
    Nonempty (Sporadic.Mathieu.M22ValueBound.ParabolicPair T) :=
  parabolicPair_of_oddCentralSplitting oddCentralSplitting_five oddCentralSplitting_three
    L C hCL hc hodd T hgen d

end Sporadic.Mathieu.M22ValueBound.OddCoverLifting
