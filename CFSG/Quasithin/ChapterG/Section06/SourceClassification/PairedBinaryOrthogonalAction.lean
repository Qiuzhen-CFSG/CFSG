module

public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.TwoFactorModelComparison
public import Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus
public import Theory.GroupTheory.DisjointCommutingProduct
public import Mathlib.LinearAlgebra.Projection

/-!
# The paired binary-plane action is the full plus orthogonal action

The two moved planes are complementary and are permuted by the original
actor. Coordinates on these planes carry their unique anisotropic forms to
the two summands of the literal binary plus four-space. The faithful actor
therefore embeds in its isometry group. The two commuting order-six factors
give a subgroup of order 36, and their interchange makes it proper, forcing
the whole group of order 72. Both the action and its two plane markings are
retained.

Source: Aschbacher–Smith, G.6.4(3)(ii) and 10.2.1, printed pp.346,743.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterG.Section06
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {a : G}

/-- The paired binary models identify the original action with the full
orthogonal action, and identify the original moved planes with its axes. -/
theorem TwoFactors.exists_paired_binary_orthogonal_action
    (d : TwoFactors ρ a)
    (h₁ : HasModelOn ρ d.first (subspaceCommutator ρ ⊤ d.first) (binaryLinearAction 2))
    (h₂ : HasModelOn ρ d.second (subspaceCommutator ρ ⊤ d.second) (binaryLinearAction 2))
    (hf : Function.Injective ρ) :
    ∃ (c : V ≃ₗ[ZMod 2] BinaryFourPlus.V)
      (e : G ≃* BinaryFourPlus.q.isometrySubgroup),
      (∀ g v, c (ρ g v) = (e g).val (c v)) ∧
      (∀ v, (c v).2 = 0 ↔ v ∈ subspaceCommutator ρ ⊤ d.first) ∧
      (∀ v, (c v).1 = 0 ↔ v ∈ subspaceCommutator ρ ⊤ d.second) := by
  classical
  let : Finite BinaryFourPlus.q.isometrySubgroup :=
    Finite.of_injective
      (fun g : BinaryFourPlus.q.isometrySubgroup => (g.val : BinaryFourPlus.V → BinaryFourPlus.V))
      (fun _ _ h => Subtype.ext (LinearEquiv.ext (congrFun h)))
  let A := subspaceCommutator ρ ⊤ d.first
  let B := subspaceCommutator ρ ⊤ d.second
  have hAB : IsCompl A B :=
    ⟨d.toTwoFactorModules.binary_plane_spaces_disjoint h₁, codisjoint_iff.mpr d.space_sum⟩
  obtain ⟨e₁,E₁,hs₁,he₁⟩ := h₁
  obtain ⟨e₂,E₂,hs₂,he₂⟩ := h₂
  let c : V ≃ₗ[ZMod 2] BinaryFourPlus.V :=
    (Submodule.prodEquivOfIsCompl A B hAB).symm.trans (E₁.prodCongr E₂)
  have hcA (v : V) : (c v).2 = 0 ↔ v ∈ A := by
    change E₂ (((Submodule.prodEquivOfIsCompl A B hAB).symm v).2) = 0 ↔ _
    rw [E₂.map_eq_zero_iff, Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero]
  have hcB (v : V) : (c v).1 = 0 ↔ v ∈ B := by
    change E₁ (((Submodule.prodEquivOfIsCompl A B hAB).symm v).1) = 0 ↔ _
    rw [E₁.map_eq_zero_iff, Submodule.prodEquivOfIsCompl_symm_apply_fst_eq_zero]
  have hunion_forward (g : G) (v : V) (hv : v ∈ A ∨ v ∈ B) :
      ρ g v ∈ A ∨ ρ g v ∈ B := by
    have hA := moved_map_conjugate ρ d.first g
    have hB := moved_map_conjugate ρ d.second g
    rcases d.permutation g with ⟨hgA,hgB⟩ | ⟨hgA,hgB⟩
    · rw [hgA] at hA
      rw [hgB] at hB
      rcases hv with hv | hv
      · left
        change ρ g v ∈ subspaceCommutator ρ ⊤ d.first
        rw [← hA]
        exact Submodule.mem_map_of_mem hv
      · right
        change ρ g v ∈ subspaceCommutator ρ ⊤ d.second
        rw [← hB]
        exact Submodule.mem_map_of_mem hv
    · rw [hgA] at hA
      rw [hgB] at hB
      rcases hv with hv | hv
      · right
        change ρ g v ∈ subspaceCommutator ρ ⊤ d.second
        rw [← hA]
        exact Submodule.mem_map_of_mem hv
      · left
        change ρ g v ∈ subspaceCommutator ρ ⊤ d.first
        rw [← hB]
        exact Submodule.mem_map_of_mem hv
  have hunion (g : G) (v : V) :
      (ρ g v ∈ A ∨ ρ g v ∈ B) ↔ (v ∈ A ∨ v ∈ B) := by
    refine ⟨fun hv => ?_, hunion_forward g v⟩
    simpa only [ρ.inv_self_apply] using hunion_forward g⁻¹ (ρ g v) hv
  have haxes : ∀ x : BinaryFourPlus.V, BinaryFourPlus.q x = 1 ↔
      x ≠ 0 ∧ (x.1 = 0 ∨ x.2 = 0) := by decide +kernel
  have hform (v : V) : BinaryFourPlus.q (c v) = 1 ↔
      v ≠ 0 ∧ (v ∈ A ∨ v ∈ B) := by
    rw [haxes, hcA, hcB, c.map_ne_zero_iff, or_comm]
  have hpres (g : G) (v : V) : BinaryFourPlus.q (c (ρ g v)) = BinaryFourPlus.q (c v) := by
    apply (by decide +kernel : ∀ x y : ZMod 2, (x = 1 ↔ y = 1) → x = y)
    rw [hform,hform,hunion]
    exact and_congr_left (fun _ => not_congr
      ⟨fun h => (ρ.apply_bijective g).injective (h.trans (map_zero (ρ g)).symm),
        fun h => h ▸ map_zero (ρ g)⟩)
  let φ : G →* (BinaryFourPlus.V ≃ₗ[ZMod 2] BinaryFourPlus.V) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) BinaryFourPlus.V).toMonoidHom.comp
      ((LinearMap.GeneralLinearGroup.congrLinearEquiv c).toMonoidHom.comp ρ.asGroupHom)
  have hφ (g : G) (w : BinaryFourPlus.V) : φ g w = c (ρ g (c.symm w)) := rfl
  let f : G →* BinaryFourPlus.q.isometrySubgroup := φ.codRestrict _ (by
    intro g
    apply (QuadraticMap.mem_isometrySubgroup BinaryFourPlus.q _).mpr
    intro w
    rw [hφ,hpres,c.apply_symm_apply])
  have hfi : Function.Injective f := by
    intro g h he
    apply hf
    apply LinearMap.ext
    intro v
    have hh := congrArg (fun z : BinaryFourPlus.q.isometrySubgroup => z.val (c v)) he
    change φ g (c v) = φ h (c v) at hh
    rw [hφ,hφ,c.symm_apply_apply] at hh
    exact c.injective hh
  have hbound : Nat.card G ≤ 72 :=
    (Nat.card_le_card_of_injective f hfi).trans_eq BinaryFourPlus.card_isometrySubgroup
  have hfirst : Nat.card d.first = 6 := by
    rw [Nat.card_congr (e₁.trans BinaryFourPlus.planeAutEquiv).toEquiv]
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  have hsecond : Nat.card d.second = 6 := by
    rw [Nat.card_congr (e₂.trans BinaryFourPlus.planeAutEquiv).toEquiv]
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  let K := d.first ⊔ d.second
  have hcomm : d.first ≤ centralizer (d.second : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp d.commute
  obtain ⟨ep,_⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting
    d.first d.second (disjoint_iff.mpr d.disjoint) hcomm
  have hK : Nat.card K = 36 := by
    rw [← Nat.card_congr ep.toEquiv, Nat.card_prod,hfirst,hsecond]
  have hne : d.first ≠ d.second := by
    intro he
    exact d.second_nontrivial (by simpa only [he,inf_idem] using d.disjoint)
  have hKN : K ≤ normalizer (d.first : Set G) :=
    sup_le d.first.le_normalizer ((commutator_eq_bot_iff_le_centralizer.mp
      (by rw [commutator_comm]; exact d.commute)).trans (centralizer_le_normalizer _))
  have hproper : K ≠ ⊤ := by
    intro he
    obtain ⟨t,_,_,_,ht⟩ := d.extension
    have hn := mem_normalizer_iff_map_conj_eq.mp (hKN (he ▸ mem_top t))
    exact hne (hn.symm.trans ht)
  have hcard : Nat.card G = 72 := by
    have hd : 36 ∣ Nat.card G := hK ▸ K.card_subgroup_dvd_card
    have hp : 0 < Nat.card G := Nat.card_pos
    have hcases : Nat.card G = 36 ∨ Nat.card G = 72 := by
      obtain ⟨k,hk⟩ := hd
      omega
    exact hcases.resolve_left (fun he => hproper (K.eq_top_of_card_eq (hK.trans he.symm)))
  have hbij : Function.Bijective f := (Nat.bijective_iff_injective_and_card f).mpr
    ⟨hfi,hcard.trans BinaryFourPlus.card_isometrySubgroup.symm⟩
  refine ⟨c,MulEquiv.ofBijective f hbij,?_,hcA,hcB⟩
  intro g v
  change c (ρ g v) = φ g (c v)
  rw [hφ,c.symm_apply_apply]

/-- The same marking with the literal wreath actor used by point stabilizers. -/
theorem TwoFactors.exists_paired_binary_wreath_action
    (d : TwoFactors ρ a)
    (h₁ : HasModelOn ρ d.first (subspaceCommutator ρ ⊤ d.first) (binaryLinearAction 2))
    (h₂ : HasModelOn ρ d.second (subspaceCommutator ρ ⊤ d.second) (binaryLinearAction 2))
    (hf : Function.Injective ρ) :
    ∃ (c : V ≃ₗ[ZMod 2] BinaryFourPlus.V) (e : G ≃* BinaryFourPlus.Wreath),
      (∀ g v, c (ρ g v) = (BinaryFourPlus.wreathToIsometry (e g)).val (c v)) ∧
      (∀ v, (c v).2 = 0 ↔ v ∈ subspaceCommutator ρ ⊤ d.first) ∧
      (∀ v, (c v).1 = 0 ↔ v ∈ subspaceCommutator ρ ⊤ d.second) := by
  obtain ⟨c,e,he,hA,hB⟩ := d.exists_paired_binary_orthogonal_action h₁ h₂ hf
  refine ⟨c,e.trans BinaryFourPlus.isometryEquivWreath,?_,hA,hB⟩
  intro g v
  simpa only [MulEquiv.trans_apply,BinaryFourPlus.wreathToIsometry_equiv] using he g v

end CFSG.Quasithin.ChapterG.Section06
