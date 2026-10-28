module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.EvenBorel.Coordinates
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.BorelPlacement
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.EmbeddingReduction.Basic
public import Theory.SpecificGroups.SL2.RootNormalizedNine

/-!
# Borel placement for the even-field ordinary-component branch

The four-module is the actual commutator [V(M₁), Xᵢ]. Since V(M₁) is a
two-group normalized by M₁=N_G(X), the commutator [V(M₁),X] lies in O₂(X).
The actual Sylow U then puts it in U ∩ K. The coordinate construction
identifies this intersection with the product of upper-unipotent groups.

The transported X has its actual E₉ quotient by O₂ and is normalized by
the full root product. The matrix normalizer theorem therefore puts the
Borel product in N_G(X)=M₁. This constructs `EvenBorelPlacement` without
assuming either Borel containment or root containment. The source adapter
retains the full marked contrary setup and proves its characteristic-normalizer
control and radical identities from uniqueness and the actual Sylow subgroup.
The stronger matrix argument obtains Borel containment directly from N_G(X);
it needs no additional characteristic subgroup of R.

The subsequent four-module bound and the final ordinary-component
elimination belong to the consuming modules.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.4.12(6)
and the ordinary-component paragraph of 15.4.20, printed pp.1160–1164.
-/

@[expose] public section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination
open Matrix.SpecialLinearGroup
variable {G : Type*} [Group G]

/-- Normalization and the actual commutator definition place the selected
source module in O₂(X), before any matrix coordinates are chosen. -/
theorem source_four_module_le_core (d : Source.Geometry G)
    (hVM : IsPGroup 2 d.VM₁) (hVM₁ : d.VM₁ ≤ d.M₁)
    (hMVM : d.M₁ ≤ normalizer (d.VM₁ : Set G)) (i : Bool) :
    d.V₁ i ≤ d.wholeX.pCoreIn 2 := by
  have hWX : ⁅d.VM₁,d.wholeX⁆ ≤ d.wholeX :=
    le_normalizer_iff_commutator_le_right.mp hVM₁
  have hWV : ⁅d.VM₁,d.wholeX⁆ ≤ d.VM₁ :=
    le_normalizer_iff_commutator_le_left.mp (d.wholeX.le_normalizer.trans hMVM)
  have hW : IsPGroup 2 (⁅d.VM₁,d.wholeX⁆ : Subgroup G) :=
    hVM.of_injective (inclusion hWV) (inclusion_injective hWV)
  have hXi : d.X i ≤ d.wholeX := by
    cases i
    · exact le_sup_left
    · exact le_sup_right
  exact (commutator_mono le_rfl hXi).trans
    (le_pCoreIn_of_normalizes hW hWX (normalizer_commutator_ge_right _ _))

/-- The core of the actual X lies in the supplied contrary Sylow subgroup;
normality is inside XU, not in the ambient group. -/
theorem source_core_le_sylow {H X U : Subgroup G}
    (hXH : X ≤ H) (hUX : U ≤ normalizer (X : Set G))
    (P : Sylow 2 H) (hP : (P : Subgroup H).map H.subtype = U) :
    X.pCoreIn 2 ≤ U := by
  have hUH : U ≤ H := hP ▸ map_subtype_le _
  have hXUH : X ⊔ U ≤ H := sup_le hXH hUH
  have hcore : X.pCoreIn 2 ≤ (X ⊔ U : Subgroup G).pCoreIn 2 :=
    pCoreIn_mono_of_normalizes le_sup_left (sup_le X.le_normalizer hUX)
  have hR := pCoreIn_le_sylow (X ⊔ U)
    (restrictSylow P hXUH (hP ▸ le_sup_right))
  rw [restrictSylow_image,hP] at hR
  exact hcore.trans hR

/-- The exact source module lies in the literal root product, and this root
product normalizes the transported X. Borel normalization remains separate. -/
theorem even_pair_source_root_coordinates [Finite G] (d : Source.Geometry G)
    {H K U : Subgroup G} (pair : OrdinaryComponentPair H K U)
    (hH : K ⊔ U = H) (hXK : d.wholeX ≤ K)
    (hUX : U ≤ normalizer (d.wholeX : Set G))
    (P : Sylow 2 H) (hP : (P : Subgroup H).map H.subtype = U)
    (hVM : IsPGroup 2 d.VM₁) (hVM₁ : d.VM₁ ≤ d.M₁)
    (hMVM : d.M₁ ≤ normalizer (d.VM₁ : Set G)) (i : Bool)
    {n : ℕ} (hm : ∀ j, ClassicalGroup.IsPSL (pair.factor j) 2 (2 ^ n)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 2 ^ n ∧
      ∃ e : K ≃* (SL(2,F) × SL(2,F)),
        let f := K.subtype.comp e.symm.toMonoidHom
        let S := (upperUnipotent F).prod (upperUnipotent F)
        S.map f = U ⊓ K ∧ d.V₁ i ≤ S.map f ∧
          S ≤ normalizer (d.wholeX.comap f : Set (SL(2,F) × SL(2,F))) := by
  obtain ⟨F,hF,hfin,hchar,hcard,e,hroot⟩ := even_pair_sylow_coordinates pair hH P hP hm
  let f := K.subtype.comp e.symm.toMonoidHom
  let S := (upperUnipotent F).prod (upperUnipotent F)
  have hVK : d.V₁ i ≤ K :=
    (source_four_module_le_core d hVM hVM₁ hMVM i).trans ((pCoreIn_le 2 _).trans hXK)
  have hVU : d.V₁ i ≤ U :=
    (source_four_module_le_core d hVM hVM₁ hMVM i).trans
      (source_core_le_sylow (hXK.trans (hH ▸ le_sup_left)) hUX P hP)
  refine ⟨F,hF,hfin,hchar,hcard,e,hroot,?_,?_⟩
  · rw [hroot]
    exact le_inf hVU hVK
  · apply le_trans _ (d.wholeX.le_normalizer_comap f)
    intro s hs
    exact hUX ((hroot ▸ mem_map_of_mem f hs).1)

/-- The four-element source module makes the actual core nontrivial. -/
theorem source_core_ne_bot (d : Source.Geometry G)
    (hVM : IsPGroup 2 d.VM₁) (hVM₁ : d.VM₁ ≤ d.M₁)
    (hMVM : d.M₁ ≤ normalizer (d.VM₁ : Set G)) (i : Bool)
    (hcard : Nat.card (d.V₁ i) = 4) : d.wholeX.pCoreIn 2 ≠ ⊥ := by
  intro h
  have he : d.V₁ i = ⊥ := le_bot_iff.mp (h ▸ source_four_module_le_core d hVM hVM₁ hMVM i)
  rw [he, card_bot] at hcard
  omega

/-- Pulling X back along its actual matrix coordinates preserves its group,
not merely its cardinality or a family label. -/
theorem source_matrix_equiv {A : Type*} [Group A] {K X : Subgroup G}
    (e : K ≃* A) (hXK : X ≤ K) :
    Nonempty (X.comap (K.subtype.comp e.symm.toMonoidHom) ≃* X) := by
  let f := K.subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := K.subtype_injective.comp e.symm.injective
  have hXr : X ≤ f.range := by
    intro x hx
    refine ⟨e ⟨x,hXK hx⟩,?_⟩
    change (e.symm (e ⟨x,hXK hx⟩) : G) = x
    rw [e.symm_apply_apply]
  have hm : (X.comap f).map f = X := map_comap_eq_self hXr
  exact ⟨(equivMapOfInjective (X.comap f) f hf).trans (MulEquiv.subgroupCongr hm)⟩

/-- The quotient in matrix coordinates is the actual source quotient by O₂.
This transport does not replace a residual with a core. -/
theorem source_matrix_core_quotient_equiv {A : Type*} [Group A] {K X : Subgroup G}
    (e : K ≃* A) (hXK : X ≤ K) :
    let C := X.comap (K.subtype.comp e.symm.toMonoidHom)
    Nonempty ((C ⧸ pCore 2 C) ≃* (X ⧸ pCore 2 X)) := by
  obtain ⟨a⟩ := source_matrix_equiv e hXK
  exact ⟨QuotientGroup.congr _ _ a (pCore_map_iso 2 a)⟩

/-- Nontriviality of the actual core survives the matrix coordinate change. -/
theorem source_matrix_core_ne_bot {A : Type*} [Group A] {K X : Subgroup G}
    (e : K ≃* A) (hXK : X ≤ K) (hX : X.pCoreIn 2 ≠ ⊥) :
    (X.comap (K.subtype.comp e.symm.toMonoidHom)).pCoreIn 2 ≠ ⊥ := by
  let C := X.comap (K.subtype.comp e.symm.toMonoidHom)
  obtain ⟨a⟩ := source_matrix_equiv e hXK
  intro hC
  have hc : pCore 2 C = ⊥ :=
    ((pCore 2 C).map_eq_bot_iff_of_injective C.subtype_injective).mp hC
  have hx : pCore 2 X = ⊥ := by
    rw [← pCore_map_iso 2 a, hc, Subgroup.map_bot]
  apply hX
  simp only [pCoreIn, hx, Subgroup.map_bot]

/-- Construct the literal Borel and root placement from the actual component
models, Sylow subgroup and source four-module. The quotient equivalence is
the earlier E₉ description of X/O₂(X), not a Borel or normalizer premise. -/
theorem even_pair_borel_placement [Finite G] (d : Source.Geometry G)
    {H K U : Subgroup G} (pair : OrdinaryComponentPair H K U)
    (hH : K ⊔ U = H) (hXK : d.wholeX ≤ K)
    (hUX : U ≤ normalizer (d.wholeX : Set G))
    (P : Sylow 2 H) (hP : (P : Subgroup H).map H.subtype = U)
    (hVM : IsPGroup 2 d.VM₁) (hVM₁ : d.VM₁ ≤ d.M₁)
    (hMVM : d.M₁ ≤ normalizer (d.VM₁ : Set G)) (i : Bool)
    (hVcard : Nat.card (d.V₁ i) = 4)
    (q : (d.wholeX ⧸ pCore 2 d.wholeX) ≃* Multiplicative (ZMod 3 × ZMod 3))
    {n : ℕ} (heven : Even n) (hn : 4 ≤ n)
    (hm : ∀ j, ClassicalGroup.IsPSL (pair.factor j) 2 (2 ^ n)) :
    EvenBorelPlacement K (d.V₁ i) d.M₁ (2 ^ n) := by
  obtain ⟨F,hF,hfin,hchar,hcard,e,hroot,hV,hS⟩ :=
    even_pair_source_root_coordinates d pair hH hXK hUX P hP hVM hVM₁ hMVM i hm
  let f := K.subtype.comp e.symm.toMonoidHom
  let C := d.wholeX.comap f
  obtain ⟨qC⟩ := source_matrix_core_quotient_equiv e hXK
  have hC : C.pCoreIn 2 ≠ ⊥ := source_matrix_core_ne_bot e hXK
    (source_core_ne_bot d hVM hVM₁ hMVM i hVcard)
  have hB := RootNormalizedNine.borel_le_normalizer C n hcard heven hn hS hC (qC.trans q)
  have hXr : d.wholeX ≤ f.range := by
    intro x hx
    refine ⟨e ⟨x,hXK hx⟩,?_⟩
    change (e.symm (e ⟨x,hXK hx⟩) : G) = x
    rw [e.symm_apply_apply]
  have hCmap : C.map f = d.wholeX := map_comap_eq_self hXr
  refine ⟨F,hF,hfin,hchar,hcard,e,?_,hV⟩
  rw [← rankOneBorel_eq_sourceBorel]
  have hmap := (map_mono (f := f) hB).trans (le_normalizer_map f)
  rwa [hCmap] at hmap

/-- Placement in the genuine contrary setup, together with the source control
of R=O₂(XU). `PlacedX` retains T₀<U<T, the actual Sylow group, the marked
S₃×S₃ map and the moved factor giving the D₈ action. Uniqueness over XT
constructs characteristic-normalizer control; no such control is assumed
for an unspecified Borel. The first conclusion discharges the even-field
placement premise of the ordinary-component elimination. -/
theorem even_pair_borel_placement_of_source [Finite G] (d : Source.Geometry G)
    {i j : Bool} {H K U : Subgroup G}
    (h : EmbeddingReduction.PlacedX d i j H U)
    (pair : OrdinaryComponentPair H K U)
    (hH : K ⊔ U = H) (hXK : d.wholeX ≤ K)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      d.wholeX ⊔ (d.T : Subgroup G) ≤ N → N = d.M₁)
    (hVM : IsElementaryAbelian 2 d.VM₁) (hVM₁ : d.VM₁ ≤ d.M₁)
    (hMVM : d.M₁ ≤ normalizer (d.VM₁ : Set G))
    (hVcard : Nat.card (d.V₁ i) = 4)
    {n : ℕ} (heven : Even n) (hn : 4 ≤ n)
    (hm : ∀ k, ClassicalGroup.IsPSL (pair.factor k) 2 (2 ^ n)) :
    EvenBorelPlacement K (d.V₁ i) d.M₁ (2 ^ n) ∧
      let R := (d.wholeX ⊔ U : Subgroup G).pCoreIn 2
      characteristicNormalizerClosure R ≤ d.M₁ ∧
        d.wholeX ⊔ (d.T : Subgroup G) ≤ normalizer (R : Set G) ∧
        R ≠ ⊥ ∧ normalizer (R : Set G) ≤ d.M₁ ∧
        (H ⊓ normalizer (R : Set G) : Subgroup G).pCoreIn 2 = R := by
  have hUX : U ≤ normalizer (d.wholeX : Set G) := h.upper.le.trans h.T_normalizes
  refine ⟨even_pair_borel_placement d pair hH hXK hUX h.sylow h.sylow_image
    hVM.isPGroup hVM₁ hMVM i hVcard h.quotient heven hn hm, ?_⟩
  have hcore := contrary_core_normalizer_control h.upper.le h.upper_index
    h.T_normalizes (source_core_ne_bot d hVM.isPGroup hVM₁ hMVM i hVcard) hunique
  exact ⟨contrary_core_characteristic_control h.upper.le h.upper_index h.T_normalizes hunique,
    normalizes_contrary_core h.upper.le h.upper_index h.T_normalizes,
    hcore.1, hcore.2, contrary_core_radical h.whole_le h.sylow h.sylow_image⟩

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination
