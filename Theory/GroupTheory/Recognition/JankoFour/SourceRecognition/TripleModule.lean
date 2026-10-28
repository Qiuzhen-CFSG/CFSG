module
public import Theory.Representation.BinaryOffender.CubicCenterChief
public import Theory.Representation.Mathieu.M22James.Classification

/-!
# Irreducibility in the minimum binary degree of the triple cover

A faithful binary action detects the cubic center on a chief section.
That section is faithful on the quasisimple triple cover, so James's
minimum degree is twelve. If the whole module has degree at most twelve,
the numerator is the whole space and the quotient map is bijective.
Thus irreducibility is a conclusion, not an additional module hypothesis.

Source: the module step in Aschbacher–Segev, *The uniqueness of groups of
type J₄*, Invent. Math. 105 (1991), (4.1), p.597, using James (1973),
Lemma 8.3. The imported James theorem proves the degree bound on the
native matrix triple cover. Application to the original core action is
in `SourceRecognition.InnerAction`.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
open Subgroup Representation Representation.BinaryOffender Sporadic.Mathieu

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem tripleCover_irreducible_of_degree_le_twelve
    (ρ : Representation (ZMod 2) M22TripleCover V) (hf : Function.Injective ρ)
    (hd : Module.finrank (ZMod 2) V ≤ 12) : ρ.IsIrreducible := by
  let T : Subgroup M22TripleCover := ⊤
  let : IsQuasisimple T := IsQuasisimple.of_mulEquiv (Subgroup.topEquiv).symm
  have hc : Nat.card (center T) = 3 :=
    (Nat.card_congr (centerCongr (Subgroup.topEquiv : T ≃* M22TripleCover)).toEquiv).trans
      M22TripleCover.center_card
  obtain ⟨U,N,hσ,hσT⟩ := exists_faithful_chief_of_cubic_center ρ T hf hc
  let σ := sectionRepresentation ρ U N
  let := hσ
  have hs : Function.Injective σ := by
    intro a b he
    have hh := hσT (show (σ.comp T.subtype) ⟨a, mem_top a⟩ =
      (σ.comp T.subtype) ⟨b, mem_top b⟩ from he)
    exact congrArg Subtype.val hh
  have hlo := M22TripleCover.faithful_irreducible_finrank_ge_twelve σ hs
  have hNle := N.toSubmodule.finrank_le
  have hQle := Submodule.finrank_quotient_le (sectionLower ρ U N).toSubmodule
  have hNdim : Module.finrank (ZMod 2) N.toSubmodule = Module.finrank (ZMod 2) V := by omega
  have hQdim : Module.finrank (ZMod 2) V =
      Module.finrank (ZMod 2) (N.toSubmodule ⧸ (sectionLower ρ U N).toSubmodule) := by omega
  have hN : N.toSubmodule = ⊤ := Submodule.eq_top_of_finrank_eq hNdim
  let j : V →ₗ[ZMod 2] N.toSubmodule := {
    toFun v := ⟨v, hN.symm ▸ Submodule.mem_top⟩
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  let f : IntertwiningMap ρ σ := {
    toLinearMap := (sectionLower ρ U N).toSubmodule.mkQ.comp j
    isIntertwining' _ := rfl }
  have hfs : Function.Surjective f := by
    intro w
    obtain ⟨v,rfl⟩ := (sectionLower ρ U N).toSubmodule.mkQ_surjective w
    exact ⟨v.val, rfl⟩
  have hfi : Function.Injective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hQdim).mpr hfs
  exact (RepEquiv.ofRepresentationEquiv (f.ofBijective ⟨hfi,hfs⟩)).irreducible_of_euqiv hσ

/-- A marking of a genuine triple cover and the degree bound suffice to
identify the entire action, without an irreducibility premise. -/
theorem tripleCover_equiv_of_degree_le_twelve
    {L : Type*} [Group L] (e : L ≃* M22TripleCover)
    (ρ : Representation (ZMod 2) L V) (hf : Function.Injective ρ)
    (hd : Module.finrank (ZMod 2) V ≤ 12) :
    ρ.IsIrreducible ∧
      Nonempty (Representation.Equiv ρ (M22TripleCover.representationOfEquiv e)) := by
  have hi := tripleCover_irreducible_of_degree_le_twelve (ρ.comp e.symm.toMonoidHom)
    (hf.comp e.symm.injective) hd
  let : ρ.IsIrreducible :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective ρ).mp hi
  have hlo := M22TripleCover.faithful_irreducible_finrank_ge_twelve_of_equiv e ρ hf
  exact ⟨inferInstance, M22TripleCover.equiv_representationOfEquiv_of_finrank_twelve
    e ρ hf (by omega)⟩

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
end
