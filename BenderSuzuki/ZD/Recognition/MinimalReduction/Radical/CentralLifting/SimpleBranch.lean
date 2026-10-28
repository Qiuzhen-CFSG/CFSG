module

public import BenderSuzuki.ZD.Recognition.MinimalReduction.Radical.CentralLifting.SimpleBranch.Projection
public import BenderSuzuki.ZD.Recognition.MinimalReduction.Radical.CentralLifting.SimpleBranch.Transport
public import Theory.GroupTheory.CentralInvolutionClassSplitting

/-!
# Reconstructing ZD when the central covering component is simple

The component's actual projection is an isomorphism onto the quotient's
simple Bender factor. Its kernel intersection is trivial. A lifted cyclic
supplement identifies the component with the ambient derived subgroup, and
generation by one involution class makes the central subgroup of order two
the entire direct factor.

The projection carries the literal intersection with `M` to the quotient
Borel because its kernel lies in `M`. Product disconnection excludes the
central generator from the distinguished class. Transport back through the
generated subgroup and odd-core quotient supplies every original ZD clause,
including both generation assertions and odd-core containment.

Source: GLS, Volume 4, Chapter 2, Lemma 4.5, final paragraph, printed p. 35
(PDF p. 52), and Theorem ZD(a–e), printed p. 21. Simplicity of the cover is
an explicit branch hypothesis, to be discharged by the central-lifting owner.
The earlier Sylow centrality and fusion hypotheses are only needed to obtain
the quotient conclusion and simplicity, so this branch does not require them.
-/

namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII SimpleBranch
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- Reconstruction of all ZD clauses in the simple-cover branch. -/
public theorem central_quotient_structure_of_simple_cover
    (h : IsProductDisconnected Z M) (hgen : Subgroup.closure Z = ⊤)
    (hclass : ∀ x ∈ Z, ∀ z ∈ Z, IsConj x z)
    (hodd : pPrimeCore 2 G = ⊥)
    (A : Subgroup G) [A.Normal] (hAc : A ≤ Subgroup.center G) (hAcard : Nat.card A = 2)
    (hs : StructureConclusion ((QuotientGroup.mk' A) '' Z) (M.map (QuotientGroup.mk' A)))
    (hK : IsSimpleGroup
      (centralLiftComponent (QuotientGroup.mk' A) (commutator (G ⧸ A)))) :
    StructureConclusion Z M := by
  let q := QuotientGroup.mk' A
  let D := commutator (G ⧸ A)
  let K := centralLiftComponent q D
  have hD : IsSimpleBenderGroup D := central_quotient_derived_model hgen hodd A hAc hAcard hs
  have hAM : A ≤ M := hAc.trans (center_le_of_productDisconnected h)
  obtain ⟨e, he⟩ := central_quotient_simple_cover_projection_equiv hgen hodd A hAc hAcard hs hK
  have heq (k : K) : (e k : G ⧸ A) = q (k : G) := congrArg Subtype.val (he k)
  have hdis : Disjoint K A := by
    apply Subgroup.disjoint_def.mpr
    intro x hxK hxA
    have hx : e ⟨x, hxK⟩ = 1 := by
      apply Subtype.ext
      rw [heq]
      exact (QuotientGroup.eq_one_iff x).mpr hxA
    exact congrArg Subtype.val (e.injective (hx.trans (map_one e).symm))
  have hgenq : Subgroup.closure (q '' Z) = ⊤ := by
    rw [← MonoidHom.map_closure, hgen,
      Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective A)]
  have hoddq : pPrimeCore 2 (G ⧸ A) = ⊥ :=
    Subgroup.pPrimeCore_quotient_eq_bot_of_central_two_subgroup A hAc
      (IsPGroup.of_card (n := 1) (by simpa using hAcard)) hodd
  obtain ⟨v, _, _, hvgen, _, _, _, hB, _⟩ :=
    (ambientConclusion_iff hgenq hoddq).mp hs
  let : Group.IsPerfect K := centralLiftComponent_perfect q
    (QuotientGroup.mk'_surjective A) (by simpa only [q, QuotientGroup.ker_mk'] using hAc) D hD
  have hder : commutator G = K := CentralInvolutionClass.derived_eq_component A K hAc
    (centralLiftComponent_map q (QuotientGroup.mk'_surjective A) D hD) v hvgen
  obtain ⟨hsup, u, huA, _, hu2, huZ, huclass⟩ := CentralInvolutionClass.split_of_one_class hgen hclass
    (fun z hz => (h.involutions z hz).sq_eq_one) (by obtain ⟨z, hz, _⟩ := h.nonempty; exact ⟨z, hz⟩)
    A K hAcard hdis hder
  have hBmap : (M.subgroupOf K).map e.toMonoidHom = (M.map q).subgroupOf D := by
    ext x
    rw [Subgroup.mem_map_equiv]
    change ((e.symm x : K) : G) ∈ M ↔ (x : G ⧸ A) ∈ M.map q
    rw [← quotient_mem_map_iff A hAM]
    have hx : q ((e.symm x : K) : G) = (x : G ⧸ A) := by
      rw [← heq, e.apply_symm_apply]
    rw [hx]
  have hborel : IsBorelSubgroup (M.subgroupOf K) := by
    have hb := hB.map_mulEquiv e.symm
    rw [← hBmap, Subgroup.map_map] at hb
    have hi : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id K := by
      apply MonoidHom.ext
      intro x
      exact e.symm_apply_apply x
    rw [hi] at hb
    have hm : (M.subgroupOf K).map (MonoidHom.id K) = M.subgroupOf K := Subgroup.map_id _
    exact hm ▸ hb
  apply (ambientConclusion_iff hgen hodd).mpr
  refine ⟨u, hAM huA, hu2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rwa [hder, huZ]
  · rwa [hder, huZ]
  · intro x hx w hw
    have hwA : w ∈ A := huZ ▸ hw
    exact Subgroup.mem_center_iff.mp (hAc hwA) x
  · exact (central_quotient_simple_cover_model hgen hodd A hAc hAcard hs hK).map_mulEquiv
      (MulEquiv.subgroupCongr hder.symm)
  · have hb := hborel.map_mulEquiv (MulEquiv.subgroupCongr hder.symm)
    have hm : (M.subgroupOf K).map (MulEquiv.subgroupCongr hder.symm).toMonoidHom =
        M.subgroupOf (commutator G) := by
      ext x
      rw [Subgroup.mem_map_equiv]
      rfl
    exact hm ▸ hb
  · intro z hz
    constructor
    · rw [hder]
      exact huclass z hz
    · intro hzu
      exact distinguished_not_mem_normal h A hAM hz (hzu.symm ▸ huA)

end BenderSuzuki.ZD
