module

public import CFSG.Quasithin.Chapter15.Section03.Constructions
public import Theory.GroupTheory.CentralizerModulo

/-!
# Subgroups in the terminal Section 15.3 amalgam

For a totally singular four-subgroup `E ≤ V`, the source uses the full
normalizer `G_E = N_G(E)`, its intersection `T_E = N_T(E)`, the residual
`Y_E = O²(N_Y(E))`, the core `Q_E = O₂(G_E)`, the conjugate span `V_E`,
and `X_E = O²(C_G(E))`. All residuals and cores are formed internally
and then embedded into the ambient group.

The temporary normalizer used in 15.3.67 is kept separate from `G_E`.
Its defining centralizer is taken in the actual quotient `G_E/E`, so
no ambient normality of `E` is imposed. The final amalgam groups use
the original `G_E` and its residual `X_E`, after that temporary
replacement has been removed.

These are constructions, without existence, recognition or Sylow claims.
Joins express generated subgroups; their equality with the source's
setwise products must be proved from the relevant normalization facts.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
printed pp.1152–1155, including PDF p.1172.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam

open Subgroup
open scoped commutatorElement
variable {G : Type*} [Group G]

/-- `G_E = N_G(E)`. -/
abbrev lineNormalizer (E : Subgroup G) : Subgroup G := normalizer (E : Set G)

/-- `M_E = N_M(E)`. -/
def lineM (M E : Subgroup G) : Subgroup G := M ⊓ lineNormalizer E

/-- `T_E = N_T(E)`; the Sylow assertion is a theorem, not part of this definition. -/
def lineT (T E : Subgroup G) : Subgroup G := T ⊓ lineNormalizer E

/-- `Y_E = O²(N_Y(E))`, using the two-residual. -/
noncomputable def lineY (Y E : Subgroup G) : Subgroup G :=
  Stellmacher.twoResidualAmbient (Y ⊓ lineNormalizer E)

/-- `Q_E = O₂(G_E)`, using the two-core. -/
noncomputable def lineQ (E : Subgroup G) : Subgroup G :=
  Stellmacher.twoCoreAmbient (lineNormalizer E)

/-- `V_E = ⟨V^{G_E}⟩`. -/
def lineV (V E : Subgroup G) : Subgroup G := conjugateSpanBy V (lineNormalizer E)

/-- `X_E = O²(C_G(E))`. -/
noncomputable def lineX (E : Subgroup G) : Subgroup G :=
  Stellmacher.twoResidualAmbient (centralizer (E : Set G))

/-- The inverse image of `C_{T_E E/E}(V_E E/E)` in `T_E`, formed in `G_E/E`.
When `E ≤ V_E ≤ G_E`, this is the source's `C_T(V_E/E)`. -/
def lineQuotientCentralizer (T V E : Subgroup G) : Subgroup G :=
  (centralizerModulo (T.subgroupOf (lineNormalizer E))
    ((lineV V E).subgroupOf (lineNormalizer E))
    (E.subgroupOf (lineNormalizer E))).map (lineNormalizer E).subtype

/-- The temporary `N_{G_E}(C_T(V_E/E))` from p.1153. -/
def temporaryLineNormalizer (T V E : Subgroup G) : Subgroup G :=
  lineNormalizer E ⊓ normalizer (lineQuotientCentralizer T V E : Set G)

/-- Right conjugation, as in the source's `F = Eˢ`. -/
def otherLine (E : Subgroup G) (s : G) : Subgroup G :=
  E.map (MulAut.conj s⁻¹).toMonoidHom

/-- `G₁ = ⟨Y_F,T_E⟩`; normalization identifies it with `Y_F T_E`. -/
noncomputable def firstAmalgamGroup (Y T E F : Subgroup G) : Subgroup G :=
  lineY Y F ⊔ lineT T E

/-- `G₂ = ⟨X_E,T_E⟩`; normalization identifies it with `X_E T_E`. -/
noncomputable def secondAmalgamGroup (T E : Subgroup G) : Subgroup G :=
  lineX E ⊔ lineT T E

/-- `G₀ = ⟨G₁,G₂⟩`, retaining the original line normalizer. -/
noncomputable def amalgamGroup (Y T E F : Subgroup G) : Subgroup G :=
  firstAmalgamGroup Y T E F ⊔ secondAmalgamGroup T E

/-- Abelianness of `V` places its line-normalizer span inside `G_E`. -/
theorem lineV_le_lineNormalizer (V E : Subgroup G) [IsMulCommutative V]
    (hEV : E ≤ V) : lineV V E ≤ lineNormalizer E := by
  have hVC : V ≤ centralizer (V : Set G) :=
    le_centralizer_iff_isMulCommutative.mpr inferInstance
  exact conjugateSpanBy_le_self
    (hVC.trans ((centralizer_le hEV).trans (centralizer_le_normalizer (E : Set G))))

/-- The quotient-centralizer construction uses only elements of `T_E`. -/
theorem lineQuotientCentralizer_le_lineT (T V E : Subgroup G) :
    lineQuotientCentralizer T V E ≤ lineT T E := by
  rintro x ⟨y, hy, rfl⟩
  exact ⟨hy.1, y.property⟩

/-- With the span inside `G_E`, membership is the genuine commutator criterion. -/
theorem mem_lineQuotientCentralizer_iff (T V E : Subgroup G)
    (hV : lineV V E ≤ lineNormalizer E) (x : G) :
    x ∈ lineQuotientCentralizer T V E ↔
      x ∈ lineT T E ∧ ∀ v ∈ lineV V E, ⁅v, x⁆ ∈ E := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hyT, hc⟩ := mem_centralizerModulo_iff.mp hy
    refine ⟨⟨hyT, y.property⟩, fun v hv => ?_⟩
    exact hc ⟨v, hV hv⟩ hv
  · rintro ⟨hx, hc⟩
    refine mem_map.mpr ⟨⟨x, hx.2⟩, ?_, rfl⟩
    exact mem_centralizerModulo_iff.mpr ⟨hx.1, fun v hv => hc v hv⟩

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam
