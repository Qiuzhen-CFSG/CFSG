module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.PointNormalizer.Kernel
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.PointNormalizer.Cartan
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.Borel
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.Cardinalities

/-!
# Point normalizers preserve the source Cartan product

Let B≤M∩Y normalize T. It preserves both L₁ and R₁. It also preserves
the actual Cartan normalizer C=N_L(T_L), so [B,X] lies in C. Since Y
is normal in G₁ and X≤G₁, these commutators lie in Y as well.

The factorization C⊆TX and coprime factor separation inside G₁ put
C∩Y in (T∩Y)X. The quotient-kernel calculation gives T∩Y≤R₁,
so B preserves R₁X. This proves the requested odd-actor result and, in
fact, does not need B to have odd order. It needs neither component
centralization nor an automorphism classification of the natural models.

The marked consumer retains the actual SL₃ or Sp₄ action, original
central quotient, and source flag equations. The preceding flag producer
supplies the Cartan Hall condition and its flag normalization; these are
not replaced by preservation of R₁X. Field four and central extensions
remain included. The final component-action application still explicitly
requires the independent field-detection input.

Source: Aschbacher--Smith 11.5.6(3), refs/quasithin.pdf,
printed pp.780--781, specifically the assertion that B₀ acts on R₁X.
-/

public section
open Subgroup
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- Coprime factor separation inside G₁ puts N_L(T_L)∩Y in R₁X.
No disjointness assumption on X and Y is necessary. -/
theorem cartanNormalizer_inter_Y_le_product (hT : (T : Subgroup G) ≤ E.G₁)
    (hX : E.X ≤ E.G₁) (hcart : LocalGeometry.IsCartan T L E.X) :
    LocalGeometry.cartanNormalizer T L ⊓ E.Y ≤ E.R₁ ⊔ E.X := by
  rintro g ⟨hg, hgY⟩
  obtain ⟨t, ht, x, hx, he⟩ := CartanActions.cartanNormalizer_factorization D hcart hg
  let H := E.G₁
  let S := (T : Subgroup G).subgroupOf H
  let X := E.X.subgroupOf H
  let Y := E.Y.subgroupOf H
  let : Y.Normal :=
    (normal_subgroupOf_iff_le_normalizer E.Y_le_G₁).mpr E.G₁_normalizes_Y
  have ho : Odd (Nat.card X) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hX).toEquiv]
    exact hcart.odd
  have hcop : Nat.Coprime (Nat.card S) (Nat.card X) := by
    have hp : IsPGroup 2 S := T.isPGroup'.comap_subtype
    obtain ⟨n, hn⟩ := hp.exists_card_eq
    rw [hn]
    exact (Nat.coprime_two_left.mpr ho).pow_left n
  let a : H := ⟨g, E.Y_le_G₁ hgY⟩
  have ha : a ∈ ((S : Set H) * (X : Set H)) ∩ Y := by
    refine ⟨⟨⟨t, hT ht⟩, ht, ⟨x, hX hx⟩, hx, ?_⟩, hgY⟩
    exact Subtype.ext he
  rw [set_mul_inter_normal_of_coprime S X Y hcop] at ha
  obtain ⟨r, hr, y, hy, hry⟩ := ha
  have hg : g = r.val * y.val := (congrArg Subtype.val hry).symm
  rw [hg]
  exact (E.R₁ ⊔ E.X).mul_mem
    (mem_sup_left (E.sylow_inter_Y_le_R₁ hT ⟨hr.1, hr.2⟩)) (mem_sup_right hy.1)

/-- The point-normalizer calculation, valid without an oddness restriction on B.
The preceding flag invariance and actual Cartan Hall condition are explicit. -/
theorem pointNormalizer_preserves_cartan_product (hT : (T : Subgroup G) ≤ E.G₁)
    (hX : E.X ≤ E.G₁) (hcart : LocalGeometry.IsCartan T L E.X)
    (B : Subgroup G) (hBM : B ≤ E.M) (hBY : B ≤ E.Y)
    (hBT : B ≤ normalizer (T : Set G)) :
    B ≤ normalizer ((E.R₁ ⊔ E.X : Subgroup G) : Set G) := by
  have hBL := (E.pointNormalizer_local_commutator B hBM hBY).1
  have hBR : B ≤ normalizer (E.R₁ : Set G) :=
    ((le_inf hBL hBT).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)).trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  have hBC := CartanActions.normalizes_cartanNormalizer hBM hBT
  have hc : ⁅B, E.X⁆ ≤ E.R₁ ⊔ E.X := by
    apply le_trans _ (E.cartanNormalizer_inter_Y_le_product hT hX hcart)
    exact le_inf
      ((commutator_mono le_rfl hcart.1).trans
        (le_normalizer_iff_commutator_le_right.mp hBC))
      ((commutator_mono hBY le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp (E.X_normalizes_Y hX)))
  apply le_normalizer_iff.mpr
  intro b hb z hz
  have hpres : E.R₁ ⊔ E.X ≤
      (E.R₁ ⊔ E.X).comap (MulAut.conj b).toMonoidHom := by
    apply sup_le
    · intro r hr
      exact mem_sup_left (le_normalizer_iff.mp hBR b hb r hr)
    · intro x hx
      have hh := (E.R₁ ⊔ E.X).mul_mem
        (hc (commutator_mem_commutator hb hx)) (mem_sup_right hx)
      change b * x * b⁻¹ ∈ E.R₁ ⊔ E.X
      simpa only [commutatorElement_def, inv_mul_cancel_right] using hh
  exact hpres hz

/-- Produce the exact interface consumed by the checked Borel contradiction. -/
theorem oddPointNormalizerAction_of_cartan (hT : (T : Subgroup G) ≤ E.G₁)
    (hX : E.X ≤ E.G₁) (hcart : LocalGeometry.IsCartan T L E.X) :
    E.OddPointNormalizerAction := by
  intro B hBM hBY hBT _
  exact E.pointNormalizer_preserves_cartan_product hT hX hcart B hBM hBY hBT

/-- Apply the calculation to the original marked SL₃/Sp₄ flag after 11.5.1.
The same binary intertwiner and central-quotient preimage identify V₁.
Cartan existence and flag normalization remain with the preceding flag producer. -/
theorem oddPointNormalizerAction_of_marked_flag (m : Nonabelian.MarkedFlag E)
    (hcart : LocalGeometry.IsCartan T L E.X)
    (hX : E.X ≤ normalizer (m.flag.Vi 0 : Set G)) :
    E.OddPointNormalizerAction := by
  have hp : E.V₁ = m.flag.Vi 0 := by
    change D.centralQuotientPreimage E.point = _
    rw [m.point_eq]
    rfl
  have hT : (T : Subgroup G) ≤ E.G₁ := by
    change (T : Subgroup G) ≤ normalizer (E.V₁ : Set G)
    rw [hp]
    exact m.flag.invariant 0
  apply E.oddPointNormalizerAction_of_cartan hT _ hcart
  change E.X ≤ normalizer (E.V₁ : Set G)
  rwa [hp]

/-- The original component-action consumer now retains only field detection
as its later model input. The independent preceding geometry is unchanged. -/
theorem component_actions_of_point_normalizer
    (hT : (T : Subgroup G) ≤ E.G₁) (hX : E.X ≤ E.G₁)
    (hcart : LocalGeometry.IsCartan T L E.X)
    (hXR : E.X ≤ normalizer (E.R₁ : Set G))
    (hCX : E.X ⊓ centralizer (E.V₁ : Set G) ≤ E.L₁)
    (hz : center (E.L₁ ⧸ pCore 2 E.L₁) = ⊥)
    (hNG : normalizer (T : Set G) ≤ E.M)
    (hdetect : E.ComponentBorelDetection)
    (I : Subgroup G) (hI : Source.ComponentIn E.Y I) :
    ⁅I, E.X⁆ ≤ E.Y.pCoreIn 2 :=
  E.component_actions_of_borel_detection hT hX hcart hXR hCX hz hNG
    (E.oddPointNormalizerAction_of_cartan hT hX hcart) hdetect I hI

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
