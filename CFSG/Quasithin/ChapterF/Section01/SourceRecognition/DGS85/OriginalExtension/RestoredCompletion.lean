module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.Completion
public import Theory.GroupTheory.Amalgam.GeneratedCompletion
public import Theory.GroupTheory.Amalgam.RankTwoCompletion.EquivTransport

/-!
# The whole restored intersection and its marked outer quotient

The two restored endpoint images intersect in exactly the original Borel
image. To prove this, decompose an element of each endpoint as an inner local
automorphism times a Borel actor. Inner Borel actors come from the reduced
Borel, and the reduced endpoint intersection is the reduced Borel. The two
endpoint images generate the constructed automorphism extension. Transporting
the original amalgam isomorphism therefore gives an actual faithful completion
in that extension, with all original maps retained.

The original Borel maps onto the outer quotient with kernel its reduced Borel.
The resulting quotient equivalence records each Borel representative, in
addition to the outer-index identity in `Completion`.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
(15.2), printed pp.226--228. Apartment-kernel preservation and recognition of
permissible regular automorphisms remain explicit source obligations.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open scoped Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
open SuzukiContainment

variable {G : Type*} [Group G]

private theorem inf_sup_of_inner (A C B N : Subgroup G)
    (hA : A ≤ N) (hC : C ≤ N) (hAB : B ≤ normalizer (A : Set G))
    (hCB : B ≤ normalizer (C : Set G))
    (hNB : N ⊓ B ≤ A) (hAC : A ⊓ C ≤ B) :
    (A ⊔ B) ⊓ (C ⊔ B) = B := by
  apply le_antisymm _ (le_inf le_sup_right le_sup_right)
  intro x hx
  obtain ⟨a,ha,b,hb,rfl⟩ := (show (x ∈ (A : Set G) * (B : Set G)) from
    (coe_mul_of_right_le_normalizer_left A B hAB) ▸ hx.1)
  obtain ⟨c,hc,d,hd,he⟩ := (show (a*b ∈ (C : Set G) * (B : Set G)) from
    (coe_mul_of_right_le_normalizer_left C B hCB) ▸ hx.2)
  change c*d=a*b at he
  change a*b ∈ B
  have heq : a⁻¹*c = b*d⁻¹ := by
    calc
      a⁻¹*c = a⁻¹*(c*d)*d⁻¹ := by group
      _ = a⁻¹*(a*b)*d⁻¹ := by rw [he]
      _ = b*d⁻¹ := by group
  have hbd : b*d⁻¹ ∈ A := hNB ⟨heq ▸ N.mul_mem (N.inv_mem (hA ha)) (hC hc),
    B.mul_mem hb (B.inv_mem hd)⟩
  have hca : c ∈ A := by
    have hh := A.mul_mem ha hbd
    rw [← heq, mul_inv_cancel_left] at hh
    exact hh
  rw [← he]
  exact B.mul_mem (hAC ⟨hca,hc⟩) hd

variable {X : Type*} [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (h : HypothesisF11 L S)
  (c : FaithfulCompletion (reducedAmalgam L S) (G := X))
  (hk : PreservesCompletionKernel h c)
  (hoverlap : c.left.range ⊓ c.right.range = c.middle.range)
  (hnormalizer : ∀ i, normalizer ((completionEndpoint c i).range : Set X) =
    (completionEndpoint c i).range)

include h hk hoverlap hnormalizer

omit hoverlap hnormalizer in
private theorem action_normalizes_innerEndpoint (i : Fin 2) :
    (completionAction h c hk).range ≤ normalizer (innerEndpoint c i : Set (MulAut X)) := by
  rintro a ⟨b,rfl⟩
  apply mem_normalizer_iff_map_conj_eq.mpr
  have he : (MulAut.conj (completionAction h c hk b)).toMonoidHom.comp MulAut.conj =
      MulAut.conj.comp (completionAction h c hk b).toMonoidHom := by
    ext x y
    simp
  change ((completionEndpoint c i).range.map MulAut.conj).map
    (MulAut.conj (completionAction h c hk b)).toMonoidHom = _
  rw [map_map, he, ← map_map, completionAction_endpoint_range]
  rfl

theorem restoredEndpoint_intersection :
    (innerEndpoint c 0 ⊔ (completionAction h c hk).range) ⊓
      (innerEndpoint c 1 ⊔ (completionAction h c hk).range) =
        (completionAction h c hk).range := by
  apply inf_sup_of_inner _ _ _ (MulAut.innerSubgroup X)
  · exact map_le_range _ _
  · exact map_le_range _ _
  · exact action_normalizes_innerEndpoint h c hk 0
  · exact action_normalizes_innerEndpoint h c hk 1
  · rintro a ⟨ha,⟨b,rfl⟩⟩
    exact (completionAction_mem_innerEndpoint_iff h c hk hoverlap hnormalizer 0 b).mpr
      ((completionAction_mem_inner_iff h c hk hoverlap hnormalizer b).mp ha)
  · change c.left.range.map MulAut.conj ⊓ c.right.range.map MulAut.conj ≤ _
    rw [← map_inf _ _ _ (conj_injective_of_center_eq_bot
      (completion_center_eq_bot h c hk hoverlap hnormalizer)), hoverlap]
    rintro a ⟨x,⟨b,rfl⟩,rfl⟩
    exact ⟨inclusion (reduced_commonBorel_le h) b, completionAction_reduced h c hk b⟩

omit hoverlap hnormalizer in
theorem restoredEndpoint_generate :
    (innerEndpoint c 0 ⊔ (completionAction h c hk).range) ⊔
      (innerEndpoint c 1 ⊔ (completionAction h c hk).range) =
        automorphismExtension h c hk := by
  change (c.left.range.map MulAut.conj ⊔ (completionAction h c hk).range) ⊔
    (c.right.range.map MulAut.conj ⊔ (completionAction h c hk).range) = _
  rw [sup_sup_sup_comm, sup_idem, ← Subgroup.map_sup, c.generated, ← MonoidHom.range_eq_map]
  rfl

/-- The quotient map on the whole original Borel into the restored outer
quotient. Its kernel is exactly the reduced Borel. -/
@[expose] def borelToOuterQuotient : commonBorel L S →*
    automorphismExtension h c hk ⧸
      (MulAut.innerSubgroup X).subgroupOf (automorphismExtension h c hk) :=
  (QuotientGroup.mk' _).comp ((completionAction h c hk).codRestrict
    (automorphismExtension h c hk) (fun b => (show (completionAction h c hk).range ≤ automorphismExtension h c hk from le_sup_right) ⟨b,rfl⟩))

theorem borelToOuterQuotient_ker : (borelToOuterQuotient h c hk).ker =
    (commonBorel L (reducedSylow L S)).subgroupOf (commonBorel L S) := by
  ext b
  change QuotientGroup.mk _ = (1 : automorphismExtension h c hk ⧸ _) ↔ _
  rw [QuotientGroup.eq_one_iff]
  exact completionAction_mem_inner_iff h c hk hoverlap hnormalizer b

omit hoverlap hnormalizer in
theorem borelToOuterQuotient_surjective : Function.Surjective (borelToOuterQuotient h c hk) := by
  intro z
  induction z using QuotientGroup.induction_on with
  | H x =>
    have hx : (x : MulAut X) ∈ (MulAut.innerSubgroup X : Set (MulAut X)) *
        ((completionAction h c hk).range : Set (MulAut X)) := by
      rw [← normal_mul]
      exact x.property
    obtain ⟨a,ha,b,⟨d,rfl⟩,he⟩ := hx
    let a' : automorphismExtension h c hk := ⟨a,(inner_le_automorphismExtension h c hk) ha⟩
    let b' : automorphismExtension h c hk :=
      ⟨completionAction h c hk d,(show (completionAction h c hk).range ≤ automorphismExtension h c hk from le_sup_right) ⟨d,rfl⟩⟩
    have he' : a'*b'=x := Subtype.ext he
    have hkill : (QuotientGroup.mk' ((MulAut.innerSubgroup X).subgroupOf
        (automorphismExtension h c hk))) a' = 1 := (QuotientGroup.eq_one_iff _).mpr ha
    refine ⟨d,?_⟩
    rw [← he']
    change _ = (QuotientGroup.mk' _) (a'*b')
    rw [map_mul,hkill,one_mul]
    rfl

/-- A marked quotient equivalence, retaining the actual image of every
original Borel element rather than just the extension index. -/
@[expose] def borelQuotientEquivOuter :
    letI := reduced_borel_normal h
    (commonBorel L S ⧸ (commonBorel L (reducedSylow L S)).subgroupOf (commonBorel L S)) ≃*
      (automorphismExtension h c hk ⧸
        (MulAut.innerSubgroup X).subgroupOf (automorphismExtension h c hk)) :=
  letI := reduced_borel_normal h
  (QuotientGroup.quotientMulEquivOfEq
    (borelToOuterQuotient_ker h c hk hoverlap hnormalizer).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (borelToOuterQuotient_surjective h c hk))

@[simp] theorem borelQuotientEquivOuter_mk (b : commonBorel L S) :
    letI := reduced_borel_normal h
    borelQuotientEquivOuter h c hk hoverlap hnormalizer (QuotientGroup.mk b) =
      borelToOuterQuotient h c hk b := by rfl

omit h hk hoverlap hnormalizer in
private theorem completion_of_marking {U D V Y : Type*}
    [Group U] [Group D] [Group V] [Group Y]
    {α : RankTwoAmalgam U D V}
    (P B Q E : Subgroup Y) (hP : B ≤ P) (hQ : B ≤ Q)
    (he : P ⊔ Q = E) (e : Iso α (ofSubgroups P B Q hP hQ)) :
    ∃ d : FaithfulCompletion α (G := E),
      (∀ x, (d.left x : Y) = e.left x) ∧
      (∀ x, (d.right x : Y) = e.right x) := by
  let d := ((FaithfulCompletion.ofGeneratedSubgroups P B Q hP hQ).mapEquiv
    (MulEquiv.subgroupCongr he)).comapIso e
  refine ⟨d, ?_, ?_⟩
  · intro x
    change ((MulEquiv.subgroupCongr he)
      ((FaithfulCompletion.ofGeneratedSubgroups P B Q hP hQ).left (e.left x)) : Y) = _
    rw [MulEquiv.subgroupCongr_apply]
    exact FaithfulCompletion.ofGeneratedSubgroups_left P B Q hP hQ (e.left x)
  · intro x
    change ((MulEquiv.subgroupCongr he)
      ((FaithfulCompletion.ofGeneratedSubgroups P B Q hP hQ).right (e.right x)) : Y) = _
    rw [MulEquiv.subgroupCongr_apply]
    exact FaithfulCompletion.ofGeneratedSubgroups_right P B Q hP hQ (e.right x)

/-- The restored automorphism extension is an actual faithful completion of
the original amalgam, retaining the full Borel and both reduced endpoint maps. -/
theorem exists_original_completion :
    ∃ d : FaithfulCompletion (originalAmalgam L S) (G := automorphismExtension h c hk),
      (∀ b : commonBorel L S, (d.middle b : MulAut X) = completionAction h c hk b) ∧
      (∀ x : parabolic L (reducedSylow L S) 0,
        (d.left (inclusion (reduced_parabolic_le h 0) x) : MulAut X) =
          MulAut.conj (c.left x)) ∧
      (∀ x : parabolic L (reducedSylow L S) 1,
        (d.right (inclusion (reduced_parabolic_le h 1) x) : MulAut X) =
          MulAut.conj (c.right x)) := by
  obtain ⟨E,hE,hleft,hright⟩ := exists_original_automorphism_iso h c hk hoverlap hnormalizer
  obtain ⟨d,hl,hr⟩ := completion_of_marking
    (innerEndpoint c 0 ⊔ (completionAction h c hk).range)
    (completionAction h c hk).range
    (innerEndpoint c 1 ⊔ (completionAction h c hk).range)
    (automorphismExtension h c hk) le_sup_right le_sup_right
    (restoredEndpoint_generate h c hk) E
  refine ⟨d, ?_, fun x => (hl _).trans (hleft x), fun x => (hr _).trans (hright x)⟩
  intro b
  change (d.left (inclusion (commonBorel_le_parabolic 0) b) : MulAut X) = _
  rw [hl]
  change (E.left ((originalAmalgam L S).left b) : MulAut X) = _
  rw [E.left_commutes]
  change (E.middle b : MulAut X) = _
  rw [hE]
  rfl

end CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
