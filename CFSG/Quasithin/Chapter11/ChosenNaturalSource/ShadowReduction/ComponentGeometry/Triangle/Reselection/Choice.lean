module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Statements
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Selection
public import Theory.SpecificGroups.SymplecticFour.SimpleQuotients
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import Theory.AtlasPort.LinearGroups.G2.Simplicity

/-!
# Choosing the literal third vertex of the field-four triangle

Both orientations in 11.1.2 give a simple two-core quotient for I. Together
with faithful maximal-local membership this reconstructs Hypothesis 12.2.3
for the same ambient group. Normalization of the two generating parabolic
residuals then permits homogeneous selection on R₂(IT), without assuming a
chosen module or invoking the later nonbinary exclusion.

Uniqueness of the other parabolic and K's relative normality give its
T-invariance. This module does not classify the new chosen module.
Source: Aschbacher--Smith 11.1.2(3), pp.762--764, and 11.4.1(2), p.776.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection
open LocalGeometry.Components
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private theorem sp_four_simple {A : Type*} [Group A]
    (h : Source.IsSp A 2 4) : IsSimpleGroup A := by
  obtain ⟨F, hF, hfin, hc, ⟨e⟩⟩ := h
  let := hF
  let := hfin
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2)
    (by simpa [← Nat.card_eq_fintype_card] using hc)
  let := Theory.SpecificGroups.SymplecticFour.SimpleQuotients.isSimpleGroup
    (F := F) (by omega)
  let : IsSimpleGroup (Matrix.symplecticGroup (Fin 2) F) :=
    Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.isSimpleGroup
  exact e.isSimpleGroup

private theorem g2_four_simple {A : Type*} [Group A]
    (h : ClassificationModels.IsG2At A 4) : IsSimpleGroup A := by
  obtain ⟨F, hF, hfin, hc, ⟨e⟩⟩ := h
  let := hF
  let := hfin
  let := Atlas.G2.isSimple (K := F) (by omega)
  exact e.isSimpleGroup

omit [Finite G] in
/-- Neither orientation is discarded when recovering simplicity of I/O₂(I). -/
theorem orientation_simple {I : Subgroup G} (h : TriangleOrientation L I) :
    IsSimpleGroup (I ⧸ pCore 2 I) := by
  rcases h with h | h
  · exact sp_four_simple h.2
  · exact g2_four_simple h.2

/-- The original global exclusions are unchanged when the faithful maximal
local component is replaced by the literal third vertex. -/
theorem hypothesis1223 (D : Chapter12.Section02.ChosenModule T L V)
    (S : D.NonbinaryNaturalInput) (I : Subgroup G)
    (hmax : I ∈ Chapter1.LStar G T)
    (hf : I ∈ MainForward.faithfulLocalComponents T)
    (ho : TriangleOrientation L I) :
    Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T I := by
  let : Group.IsPerfect I := Chapter1.mem_L_isPerfect hmax.1
  let : IsSimpleGroup (I ⧸ pCore 2 I) := orientation_simple ho
  have hcenter : center (I ⧸ pCore 2 I) = ⊥ := by
    rcases (inferInstance : (center (I ⧸ pCore 2 I)).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact False.elim (Group.IsPerfect.not_isMulCommutative (I ⧸ pCore 2 I)
        (center_eq_top_iff.mp h))
  exact {
    simpleQTKE := S.source.simpleQTKE
    maximal_faithful := ⟨hmax, hf.2⟩
    quasisimple := {
      toIsPerfect := inferInstance
      simple := ((QuotientGroup.quotientMulEquivOfEq hcenter).trans
        QuotientGroup.quotientBot).isSimpleGroup }
    no_rankTwo := S.source.no_rankTwo
    no_M22 := S.source.no_M22
    no_M23 := S.source.no_M23
    no_J4 := S.source.no_J4 }

omit [Finite G] in
/-- Uniqueness of the other parabolic in K makes it T-invariant.
Only K's earlier relative normality is needed; K₀-invariance is derived. -/
theorem other_parabolic_normalized
    {K K₀ L₁ : Subgroup G} (hK₀ : K₀ ∈ Chapter1.L G T)
    (hle : K₀ ≤ K) (hne : K₀ ≠ K) (hne₁ : K₀ ≠ L₁)
    (hu : ∀ J : Subgroup G, J ∈ Chapter1.L G T → J ≤ K →
      J ≠ K → J ≠ L₁ → J = K₀)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hTL₁ : (T : Subgroup G) ≤ normalizer (L₁ : Set G)) :
    (T : Subgroup G) ≤ normalizer (K₀ : Set G) := by
  intro t ht
  apply mem_normalizer_iff_map_conj_eq.mpr
  let e := MulAut.conj t
  have hTe : (T : Subgroup G).map e.toMonoidHom = T :=
    mem_normalizer_iff_map_conj_eq.mp ((T : Subgroup G).le_normalizer ht)
  have hKe : K.map e.toMonoidHom = K := mem_normalizer_iff_map_conj_eq.mp (hTK ht)
  have hL₁e : L₁.map e.toMonoidHom = L₁ := mem_normalizer_iff_map_conj_eq.mp (hTL₁ ht)
  apply hu
  · rw [← hTe]
    exact (Chapter1.mem_L_map_iff e.toMonoidHom e.injective).mpr hK₀
  · exact (map_mono hle).trans hKe.le
  · intro he
    apply hne
    exact map_injective e.injective (he.trans hKe.symm)
  · intro he
    apply hne₁
    exact map_injective e.injective (he.trans hL₁e.symm)

/-- Construct the new Irr⁺ module from the triangle, retaining the literal
join K₀ ∨ L₂ and both possible quotient orientations. -/
theorem exists_triangle_choice (D : Chapter12.Section02.ChosenModule T L V)
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (K X : Subgroup G)
    (htriangle : FieldFourTriangle T L (f.Li 0) (f.Li 1) K X)
    (hKnormal : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K) :
    ∃ K₀ : Subgroup G, K₀ ∈ Chapter1.L G T ∧ K₀ ≤ K ∧ K₀ ≠ K ∧ K₀ ≠ f.Li 0 ∧
      TriangleOrientation L (K₀ ⊔ f.Li 1) ∧
      Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T (K₀ ⊔ f.Li 1) ∧
      ∃ U : Subgroup G, Nonempty (Chapter12.Section02.ChosenModule T (K₀ ⊔ f.Li 1) U) := by
  obtain ⟨_, K₀, hK, hle, hne, hne₁, hu, hmax, hf, ho⟩ := htriangle
  have hTK : (T : Subgroup G) ≤ normalizer (K : Set G) :=
    (f.invariant 0).trans ((normal_subgroupOf_iff_le_normalizer hKnormal.1.1).mp hKnormal.2)
  have hTK₀ := other_parabolic_normalized hK hle hne hne₁ hu hTK (f.sylow_normalizes_Li 0)
  have hTI : (T : Subgroup G) ≤ normalizer ((K₀ ⊔ f.Li 1 : Subgroup G) : Set G) :=
    (le_inf hTK₀ (f.sylow_normalizes_Li 1)).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hI := hypothesis1223 D S (K₀ ⊔ f.Li 1) hmax hf ho
  exact ⟨K₀, hK, hle, hne, hne₁, ho, hI,
    hI.toHypothesis1221.exists_chosen_of_normalizes hTI⟩

/-- The other vertex escapes N_G(L) because otherwise both generators of
K would lie there. The generation identity is the one proved on p.762. -/
theorem third_vertex_escapes (D : Chapter12.Section02.ChosenModule T L V)
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (K K₀ : Subgroup G) (hgen : K = f.Li 0 ⊔ K₀)
    (hout : ¬ K ≤ normalizer (L : Set G)) :
    ¬ K₀ ⊔ f.Li 1 ≤ normalizer (L : Set G) := by
  intro h
  apply hout
  rw [hgen]
  exact sup_le ((LocalGeometry.localResidual_le _).trans
    (inf_le_left.trans L.le_normalizer)) (le_sup_left.trans h)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection
