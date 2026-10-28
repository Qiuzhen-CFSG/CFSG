module

public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.IrreducibleReconstruction.SectionKernel
public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.AmbientPlacement
public import Theory.Representation.SymplecticFourBinaryNormalizer
public import Theory.GroupTheory.CComponent.QuasisimpleFactors

/-!
# Ambient conjugation on the actual central moved quotient

When the moved space is the whole original module and its actor is
characteristic in a normal subgroup, every ambient operator preserves the
literal fixed kernel. It therefore induces a quotient automorphism which
intertwines ambient conjugation. In the binary symplectic row, the natural
normalizer theorem makes that conjugation inner; G.6 displacement generation
then removes the centralizer and proves that the normal closure is all of G.

Source: Aschbacher–Smith, G.6.4, printed pp.345–346.
-/

public section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterG.Section06
open ChapterB.QuasisimpleSource IrreducibleReconstruction
universe u v

namespace IrreducibleReconstruction
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {ρ : Representation (ZMod 2) G V}

theorem exists_ambient_intertwiner (K : Subgroup G) [K.Normal]
    (L : Subgroup K) [L.Characteristic]
    (s : MovedSection (ρ.comp K.subtype) L) (hs : s.space.toSubmodule = ⊤) (g : G) :
    ∃ f : (s.space.toSubmodule ⧸ s.central.toSubmodule) ≃ₗ[ZMod 2]
        (s.space.toSubmodule ⧸ s.central.toSubmodule),
      ∀ (k : K) (v : s.space.toSubmodule ⧸ s.central.toSubmodule),
        f (MovedSection.action (ρ.comp K.subtype) s k v) =
          MovedSection.action (ρ.comp K.subtype) s (MulAut.conjNormal g k) (f v) := by
  let A : s.space.toSubmodule ≃ₗ[ZMod 2] s.space.toSubmodule :=
    (topSpaceEquiv s hs).symm.trans
      ((SymplecticConjugatePair.Ambient.linearAction ρ g).trans (topSpaceEquiv s hs))
  have hstable : s.central.toSubmodule.map A.toLinearMap ≤ s.central.toSubmodule := by
    rintro _ ⟨v, hv, rfl⟩
    rw [s.central_eq] at hv ⊢
    intro l
    apply Subtype.ext
    have he := congrArg Subtype.val
      (hv (MulAut.characteristic L (MulAut.conjNormal g⁻¹) l))
    change ρ ((MulAut.conjNormal g⁻¹) (l : K) : K) v.val = v.val at he
    change ρ (l : K) (ρ g v.val) = ρ g v.val
    calc
      _ = ρ g (ρ ((MulAut.conjNormal g⁻¹) (l : K) : K) v.val) := by
        simp only [MulAut.conjNormal_apply, inv_inv, ← Module.End.mul_apply,
          ← map_mul, mul_inv_cancel_left, mul_assoc]
      _ = _ := congrArg (ρ g) he
  have hmap : s.central.toSubmodule.map A.toLinearMap = s.central.toSubmodule :=
    Submodule.eq_of_le_of_finrank_eq hstable (A.finrank_map_eq _)
  let f := Submodule.Quotient.equiv s.central.toSubmodule s.central.toSubmodule A hmap
  refine ⟨f, ?_⟩
  intro k v
  induction v using Submodule.Quotient.induction_on with
  | _ v =>
    change s.central.toSubmodule.mkQ (A (s.space.toRepresentation k v)) =
      s.central.toSubmodule.mkQ (s.space.toRepresentation (MulAut.conjNormal g k) (A v))
    congr 1
    apply Subtype.ext
    change ρ g (ρ k v.val) = ρ (MulAut.conjNormal g k : K) (ρ g v.val)
    simp only [MulAut.conjNormal_apply, ← Module.End.mul_apply, ← map_mul,
      inv_mul_cancel_right]
end IrreducibleReconstruction

variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {κ : GroupClass.{u}} {ρ : Representation (ZMod 2) G V} {a : G}
  {Cover : Type u} [Group Cover] {q : Cover →* G}

theorem Hypotheses.normalClosure_eq_top_of_symplectic_section
    (h : Hypotheses κ ρ a q)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1)
    (s : MovedSection (ρ.comp (normalClosure ({a} : Set G)).subtype)
      (generalizedFitting (normalClosure ({a} : Set G))))
    (hs : s.space.toSubmodule = ⊤)
    (e : ActionEquiv s.action (symplecticNatural (k := ZMod 2) 2)) :
    normalClosure ({a} : Set G) = ⊤ := by
  let := h.finite_module
  let K := normalClosure ({a} : Set G)
  apply top_unique
  intro g _
  obtain ⟨f, hf⟩ := exists_ambient_intertwiner K (generalizedFitting K) s hs g
  let F := e.linearEquiv.symm.trans (f.trans e.linearEquiv)
  let φ := MulAut.congr e.groupEquiv (MulAut.conjNormal g)
  have hF (k : Theory.SpecificGroups.SymplecticFour.Sp (ZMod 2)) (v) :
      F (symplecticNatural 2 k v) = symplecticNatural 2 (φ k) (F v) := by
    obtain ⟨l, rfl⟩ := e.groupEquiv.surjective k
    obtain ⟨w, rfl⟩ := e.linearEquiv.surjective v
    change e.linearEquiv (f (e.linearEquiv.symm _)) = _
    rw [← e.intertwines, e.linearEquiv.symm_apply_apply, hf, e.intertwines]
    simp only [φ, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, F,
      LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    rfl
  obtain ⟨b, hb⟩ := Representation.SymplecticFourBinaryNormalizer.automorphism_inner F φ hF
  have hi : MulAut.conj (e.groupEquiv.symm b) = (MulAut.conjNormal g : MulAut K) := by
    apply (MulAut.congr e.groupEquiv).injective
    rw [MulAut.congr_conj, e.groupEquiv.apply_symm_apply]
    exact hb
  have hm : g ∈ (MulAut.innerSubgroup K).comap MulAut.conjNormal :=
    ⟨e.groupEquiv.symm b, hi⟩
  rw [MulAut.conjNormal_comap_innerSubgroup,
    h.rank_one_centralizer_normalClosure_eq_bot hr, sup_bot_eq] at hm
  exact hm

end CFSG.Quasithin.ChapterG.Section06
