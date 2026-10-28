module

public import Theory.GroupTheory.PCoreFrattiniAction
public import Theory.GroupTheory.ExtraspecialSquare
public import Theory.GroupTheory.PGroup.ExtraspecialAutomorphisms
public import Theory.Representation.BinaryConjugationSection.QuotientActor
public import Theory.Representation.BinaryOffender.CubicCenterChief
public import Theory.Representation.Mathieu.M22James.Classification

/-!
# Actions used by the full Mathieu centralizer quotient

The Frattini-action kernel identifies the faithful conjugation action on
an extraspecial core modulo its center. A marked section with the same
kernel then gives coordinates for the full image core. Finally a faithful
chief factor for the cubic center, together with James's minimum degree,
forces any faithful binary degree-twelve representation of 3·M₂₂ to be
irreducible. These action interfaces are applied to the original chosen
module in NonFFSourceMathieuM24FullQuotient.

Source: Aschbacher–Smith 8.2.13 and H.12.1, printed pp.722–723.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Sporadic.Mathieu
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuSextet

private theorem quotientAut_kernel_eq {P : Type*} [Group P]
    (U V : Subgroup P) [U.Characteristic] [V.Characteristic] (h : U = V) :
    (quotientAut U).ker = (quotientAut V).ker := by
  subst V
  rfl

/-- A self-centralizing extraspecial two-core gives a faithful action of the full
core quotient on its central quotient, with the literal conjugation formula. -/
theorem faithful_core_action {C : Type*} [Group C] [Finite C]
    [IsExtraspecial 2 (pCore 2 C)]
    (hc : centralizer (pCore 2 C : Set C) ≤ pCore 2 C) :
    ∃ ρ : Representation (ZMod 2) (C ⧸ pCore 2 C)
      (ExtraspecialSquare.Space (pCore 2 C)),
      Function.Injective ρ ∧
      ∀ (c : C) (x : pCore 2 C),
        ρ (QuotientGroup.mk' (pCore 2 C) c)
          (Additive.ofMul (QuotientGroup.mk' (center (pCore 2 C)) x)) =
        Additive.ofMul (QuotientGroup.mk' (center (pCore 2 C)) (MulAut.conjNormal c x)) := by
  let P := pCore 2 C
  let α := (quotientAut (center P)).comp (MulAut.conjNormal : C →* MulAut P)
  have hker : α.ker = P := by
    have hh := pCore_frattini_action_kernel 2 hc
    have he := quotientAut_kernel_eq (frattini P) (center P)
      (IsExtraspecial.frattini_eq_center (p := 2) (P := P))
    change (α : C →* MulAut (P ⧸ center P)).ker = P
    change (center P).quotientAut.ker.comap (MulAut.conjNormal : C →* MulAut P) = P
    rw [←he]
    exact hh
  let β : (C ⧸ P) →* MulAut (P ⧸ center P) := QuotientGroup.lift P α hker.ge
  have hb : Function.Injective β := (QuotientGroup.injective_lift_iff _ _ _).mpr hker.symm
  let ρ : Representation (ZMod 2) (C ⧸ P) (ExtraspecialSquare.Space P) := {
    toFun c := (β c).toMonoidHom.toAdditive.toZModLinearMap 2
    map_one' := by ext v; change β 1 v.toMul = v.toMul; rw [map_one]; rfl
    map_mul' c d := by ext v; change β (c*d) v.toMul = β c (β d v.toMul); rw [map_mul]; rfl }
  refine ⟨ρ,?_,?_⟩
  · intro c d he
    apply hb
    ext v
    exact congrArg (fun f : Module.End (ZMod 2) (ExtraspecialSquare.Space P) =>
      (f (Additive.ofMul v)).toMul) he
  · intro c x
    change Additive.ofMul (quotientAut (center P) (MulAut.conjNormal c)
      (QuotientGroup.mk' (center P) x)) = _
    rw [quotientAut_apply_mk]

/-- A surjective section map with the marked kernel identifies the whole two-core
with the marked module, preserving the original conjugation action. -/
theorem core_coordinates {G H M : Type*} [Group G] [Group H]
    [AddCommGroup M] [Module (ZMod 2) M]
    (R V W : Subgroup G) {ρ : Representation (ZMod 2) R M}
    (d : BinaryConjugationSection R V W ρ)
    (f : R →* H) (g : V →* pCore 2 H) (hg : Function.Surjective g)
    (hgval : ∀ v, (g v : H) = f (inclusion d.section_le v))
    (hk : g.ker = d.coordinates.ker) :
    ∃ e : pCore 2 H ≃* Multiplicative M,
      (∀ v, e (g v) = d.coordinates v) ∧
      ∀ (r : R) (v : pCore 2 H),
        (e (MulAut.conjNormal (f r) v)).toAdd = ρ r (e v).toAdd := by
  let e := (QuotientGroup.quotientKerEquivOfSurjective g hg).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hk).trans
      (QuotientGroup.quotientKerEquivOfSurjective d.coordinates d.onto))
  have he (v : V) : e (g v) = d.coordinates v := by
    change (QuotientGroup.quotientKerEquivOfSurjective d.coordinates d.onto)
      ((QuotientGroup.quotientMulEquivOfEq hk)
        ((QuotientGroup.quotientKerEquivOfSurjective g hg).symm (g v))) = _
    rw [show g v = (QuotientGroup.quotientKerEquivOfSurjective g hg)
      (QuotientGroup.mk' g.ker v) from rfl, MulEquiv.symm_apply_apply]
    rfl
  refine ⟨e,he,?_⟩
  intro r v
  obtain ⟨w,rfl⟩ := hg v
  have hc : MulAut.conjNormal (f r) (g w) =
      g ⟨(r : G)*(w : G)*(r : G)⁻¹,
        (mem_normalizer_iff.mp (d.normalized r.property) w).mp w.property⟩ := by
    apply Subtype.ext
    change f r*(g w : H)*(f r)⁻¹ = _
    rw [hgval,hgval]
    change f r*f (inclusion d.section_le w)*(f r)⁻¹ =
      f (r*(inclusion d.section_le w)*r⁻¹)
    simp only [map_mul,map_inv]
  rw [hc,he,he]
  exact d.equivariant r w

/-- A faithful binary representation of the concrete triple cover in dimension
twelve is irreducible: its faithful chief factor already has dimension twelve. -/
theorem triple_cover_irreducible {A M : Type*} [Group A] [Finite A]
    [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
    (e : A ≃* M22TripleCover) (ρ : Representation (ZMod 2) A M)
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) M = 12) :
    IsIrreducible ρ := by
  let : IsQuasisimple A := IsQuasisimple.of_mulEquiv e.symm
  let : IsQuasisimple (⊤ : Subgroup A) := IsQuasisimple.of_mulEquiv topEquiv.symm
  have hc : Nat.card (center (⊤ : Subgroup A)) = 3 :=
    (Nat.card_congr (centerCongr (topEquiv.trans e)).toEquiv).trans M22TripleCover.center_card
  obtain ⟨U,N,hirr,hfaith⟩ := exists_faithful_chief_of_cubic_center ρ ⊤ hf hc
  let τ := sectionRepresentation ρ U N
  let := hirr
  have hτ : Function.Injective τ := by
    intro x y he
    have hh := hfaith (a₁ := (⟨x,mem_top _⟩ : (⊤ : Subgroup A)))
      (a₂ := (⟨y,mem_top _⟩ : (⊤ : Subgroup A))) he
    exact congrArg Subtype.val hh
  have hlo := M22TripleCover.faithful_irreducible_finrank_ge_twelve_of_equiv e τ hτ
  let Z := (sectionLower ρ U N).toSubmodule
  have hle : Module.finrank (ZMod 2) (N.toSubmodule ⧸ Z) ≤
      Module.finrank (ZMod 2) N.toSubmodule := Submodule.finrank_quotient_le Z
  have hn := N.toSubmodule.finrank_le
  have hdim : Module.finrank (ZMod 2) N.toSubmodule = Module.finrank (ZMod 2) M := by
    change 12 ≤ Module.finrank (ZMod 2) (N.toSubmodule ⧸ Z) at hlo
    omega
  have hN : N.toSubmodule = ⊤ := Submodule.eq_top_of_finrank_eq hdim
  let q : IntertwiningMap N.toRepresentation τ := {
    toLinearMap := Z.mkQ
    isIntertwining' _ := rfl }
  have hq : Function.Bijective q := by
    have hdimQ : Module.finrank (ZMod 2) N.toSubmodule =
        Module.finrank (ZMod 2) (N.toSubmodule ⧸ Z) := by
      change 12 ≤ Module.finrank (ZMod 2) (N.toSubmodule ⧸ Z) at hlo
      omega
    exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdimQ).mpr Z.mkQ_surjective,
      Z.mkQ_surjective⟩
  let i : IntertwiningMap N.toRepresentation ρ := {
    toLinearMap := N.toSubmodule.subtype
    isIntertwining' _ := rfl }
  have hi : Function.Bijective i := ⟨Subtype.val_injective,fun v => ⟨⟨v,hN.symm ▸
    (show v ∈ (⊤ : Submodule (ZMod 2) M) from trivial)⟩,rfl⟩⟩
  exact (RepEquiv.ofRepresentationEquiv
    ((i.ofBijective hi).symm.trans (q.ofBijective hq))).irreducible_of_euqiv hirr

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuSextet
