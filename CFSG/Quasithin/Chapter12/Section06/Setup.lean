module

public import CFSG.Quasithin.Chapter12.Section02.SourceHypotheses
public import Theory.Representation.BinaryPermutationAlternatingActions
public import Theory.Representation.BinaryPermutation.TerminalOrthogonal.EightCoordinates
public import Theory.Representation.SubspaceQuotient
public import Theory.GroupTheory.PResidual.PrimeTo
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Theory.GroupTheory.SolvableResidual
public import Theory.GroupTheory.PGroup.OmegaAmbient
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Literal setup for nonsingular centralizers in Section 12.6

The input is Hypothesis 12.2.3 and its original chosen Irr⁺ member, together
with the section's A₈ quotient and equivariant orthogonal-module marking.
The group quotient is by the kernel of the actual conjugation action on V;
its equality with C_L(V) is proved below. The linear quotient uses the
actual fixed space, whose ambient image is proved to be C_V(L). Its
quadratic form is the half-weight form on the six-dimensional permutation
section, with the existing isometry to the split six-space.

All local subgroups are literal constructions in the common ambient group.
L_v is the two-residual O²(C_L(v)); L_v^∞ is defined separately. Likewise
O₂(L), O₂,Z(L), and the action kernel remain separate until the source
bridge is proved. K_v is the canonical O^{3′}(G_v^∞) candidate: its relative
normality follows from the construction, but its C-component membership,
containment of L_v and quasisimple quotient are not assumed or asserted here.
R uses the quotient action before Lemma 12.6.5, not its later simplified
centralizer. No Sylow alignment is built into the source hypothesis.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Notation 12.2.5, printed p.796, and Section 12.6, printed pp.822–828.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section06
universe u
variable {G : Type u} [Group G]

/-- The source maximal overgroup N_G(L). -/
def M (L : Subgroup G) : Subgroup G := normalizer (L : Set G)
/-- The join LT; its product interpretation follows after T-normalization. -/
def LT (T : Sylow 2 G) (L : Subgroup G) : Subgroup G := L ⊔ (T : Subgroup G)
/-- The source two-core O₂(LT) in G. -/
def Q (T : Sylow 2 G) (L : Subgroup G) : Subgroup G := (LT T L).pCoreIn 2
/-- The fixed subgroup C_V(L), in the original ambient group. -/
def ZV (L V : Subgroup G) : Subgroup G := V ⊓ centralizer (L : Set G)
/-- The actual centralizer C_G(v). -/
def Gv (v : G) : Subgroup G := centralizer ({v} : Set G)
/-- The relative centralizer C_M(v). -/
def Mv (L : Subgroup G) (v : G) : Subgroup G := M L ⊓ Gv v
/-- The relative centralizer C_T(v), before any Sylow re-selection. -/
def Tv (T : Sylow 2 G) (v : G) : Subgroup G := (T : Subgroup G) ⊓ Gv v
/-- The relative centralizer C_L(v). -/
def CLv (L : Subgroup G) (v : G) : Subgroup G := L ⊓ Gv v
/-- Notation 12.2.5 uses the two-residual, not the two-core. -/
def Lv (L : Subgroup G) (v : G) : Subgroup G :=
  (pResidual 2 (CLv L v)).map (CLv L v).subtype
/-- The separate perfect residual C_L(v)^∞. Its equality with L_v needs proof. -/
def LvInfinity (L : Subgroup G) (v : G) : Subgroup G :=
  (solvableResidual (CLv L v)).map (CLv L v).subtype
/-- The literal two-core O₂(C_LT(v)). -/
def Rv (T : Sylow 2 G) (L : Subgroup G) (v : G) : Subgroup G :=
  (LT T L ⊓ Gv v).pCoreIn 2
/-- The moved subgroup [V,L_v]. -/
def Vv (L V : Subgroup G) (v : G) : Subgroup G := ⁅V, Lv L v⁆
/-- The canonical component candidate O^{3′}(G_v^∞), embedded in G. -/
def Kv (v : G) : Subgroup G :=
  ((primeToResidual 3 (solvableResidual (Gv v))).map
    (solvableResidual (Gv v)).subtype).map (Gv v).subtype

/-- O₂,Z(L): the preimage of Z(L/O₂(L)), without identifying it with O₂(L). -/
def twoCentralCore (L : Subgroup G) : Subgroup L :=
  (center (L ⧸ pCore 2 L)).comap (QuotientGroup.mk' (pCore 2 L))

/-- The literal quotient H/O₂(H). -/
abbrev Star (H : Subgroup G) := H ⧸ pCore 2 H

/-- The image of A∩H under the actual core quotient map. -/
def starImage (H A : Subgroup G) : Subgroup (Star H) :=
  (A.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))

/-- Elements normalizing A and acting trivially on A/O₂(A). -/
def coreQuotientCentralizer (A : Subgroup G) : Subgroup G :=
  (((quotientAut (pCore 2 A)).comp A.normalizerMonoidHom).ker).map
    (normalizer (A : Set G)).subtype

/-- The original R=C_S(L_v*/O₂(L_v*)) in the quotient of K S. -/
def R (L K S : Subgroup G) (v : G) : Subgroup G :=
  S ⊓ ((coreQuotientCentralizer (starImage (K ⊔ S) (Lv L v))).comap
    (QuotientGroup.mk' (pCore 2 (K ⊔ S : Subgroup G)))).map (K ⊔ S).subtype

/-- Z=Ω₁(Z(T)), with its intrinsic center embedded in G. -/
def Z (T : Sylow 2 G) : Subgroup G :=
  omegaOneAmbient ((center (T : Subgroup G)).map (T : Subgroup G).subtype)

/-- U=Ω₁(Z(O₂(K S))), again embedded in G. -/
def U (K S : Subgroup G) : Subgroup G :=
  omegaOneAmbient ((center ((K ⊔ S).pCoreIn 2)).map ((K ⊔ S).pCoreIn 2).subtype)

/-- Conjugation by L on the original subgroup V. -/
def conjugation (L V : Subgroup G) (hn : L ≤ normalizer (V : Set G)) :
    L →* MulAut V := V.normalizerMonoidHom.comp (inclusion hn)

/-- Linearize the actual conjugation action on the elementary two-group V. -/
noncomputable def seedRepresentation (L V : Subgroup G) [IsElementaryAbelian 2 V]
    (hn : L ≤ normalizer (V : Set G)) : Representation (ZMod 2) L (Additive V) :=
  Representation.elementaryRepresentation (conjugation L V hn)

/-- The invariant subrepresentation giving the literal fixed-space quotient. -/
noncomputable def fixedSeed (L V : Subgroup G) [IsElementaryAbelian 2 V]
    (hn : L ≤ normalizer (V : Set G)) : Subrepresentation (seedRepresentation L V hn) where
  toSubmodule := (seedRepresentation L V hn).invariants
  apply_mem_toSubmodule g v hv := by
    rw [Representation.mem_invariants] at hv
    rw [hv g]
    exact hv

/-- The linear quotient V/C_V(L). See mem_fixedSeed_iff for the ambient comparison. -/
abbrev Vhat (L V : Subgroup G) [IsElementaryAbelian 2 V]
    (hn : L ≤ normalizer (V : Set G)) :=
  Additive V ⧸ (fixedSeed L V hn).toSubmodule

/-- The actual A₈ quotient and equivariant natural-module coordinates. -/
structure OrthogonalMarking (L V : Subgroup G) [IsElementaryAbelian 2 V]
    (hn : L ≤ normalizer (V : Set G)) where
  groupEquiv : (L ⧸ (conjugation L V hn).ker) ≃* alternatingGroup (Fin 8)
  coordinates : Vhat L V hn ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 8)
  equivariant : ∀ (l : L) (w : Vhat L V hn),
    coordinates ((fixedSeed L V hn).quotientRepresentation l w) =
      BinaryPermutation.alternatingNaturalRepresentation (Fin 8)
        (groupEquiv (QuotientGroup.mk' (conjugation L V hn).ker l)) (coordinates w)

/-- The genuine section assumptions, with no later local conclusions. -/
structure SourceHypothesis [Finite G] (K : GroupClass.{u})
    (T : Sylow 2 G) (L V : Subgroup G) where
  source : Section02.Hypothesis1223 K T L
  chosen : Section02.ChosenModule T L V
  orthogonal : letI := chosen.elementary
    Nonempty (OrthogonalMarking L V chosen.normalizes)

/-- Nonsingularity of the image of v in the marked orthogonal quotient. -/
def OrthogonalMarking.Nonsingular {L V : Subgroup G} [IsElementaryAbelian 2 V]
    {hn : L ≤ normalizer (V : Set G)} (D : OrthogonalMarking L V hn) (v : V) : Prop :=
  BinaryPermutation.TerminalOrthogonal.Eight.form
    (D.coordinates (Submodule.Quotient.mk (Additive.ofMul v))) ≠ 0

theorem conjugation_ker (L V : Subgroup G) (hn : L ≤ normalizer (V : Set G)) :
    (conjugation L V hn).ker = (centralizer (V : Set G)).subgroupOf L := by
  ext l
  change conjugation L V hn l = 1 ↔ (l : G) ∈ centralizer (V : Set G)
  constructor
  · intro h
    rw [mem_centralizer_iff]
    intro v hv
    have he := congrArg (fun f : MulAut V => (f ⟨v, hv⟩ : G)) h
    change (l : G) * v * (l : G)⁻¹ = v at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro h
    apply MulEquiv.ext
    intro v
    apply Subtype.ext
    change (l : G) * (v : G) * (l : G)⁻¹ = v
    rw [← mem_centralizer_iff.mp h v v.property, mul_inv_cancel_right]

theorem mem_fixedSeed_iff (L V : Subgroup G) [IsElementaryAbelian 2 V]
    (hn : L ≤ normalizer (V : Set G)) (v : Additive V) :
    v ∈ (fixedSeed L V hn).toSubmodule ↔ (v.toMul : G) ∈ ZV L V := by
  change (∀ l : L, seedRepresentation L V hn l v = v) ↔ _
  constructor
  · intro h
    refine ⟨v.toMul.property, mem_centralizer_iff.mpr ?_⟩
    intro l hl
    have he := congrArg (fun x : Additive V => (x.toMul : G)) (h ⟨l, hl⟩)
    change l * (v.toMul : G) * l⁻¹ = v.toMul at he
    exact mul_inv_eq_iff_eq_mul.mp he
  · rintro ⟨_, hv⟩ l
    apply Additive.toMul.injective
    apply Subtype.ext
    change (l : G) * (v.toMul : G) * (l : G)⁻¹ = v.toMul
    rw [mem_centralizer_iff.mp hv l l.property, mul_inv_cancel_right]

theorem nonsingular_ne_one {L V : Subgroup G} [IsElementaryAbelian 2 V]
    {hn : L ≤ normalizer (V : Set G)} (D : OrthogonalMarking L V hn)
    {v : V} (hv : D.Nonsingular v) : v ≠ 1 := by
  intro he
  apply hv
  subst v
  change BinaryPermutation.TerminalOrthogonal.Eight.form (D.coordinates 0) = 0
  simp

theorem nonsingular_not_mem_ZV {L V : Subgroup G} [IsElementaryAbelian 2 V]
    {hn : L ≤ normalizer (V : Set G)} (D : OrthogonalMarking L V hn)
    {v : V} (hv : D.Nonsingular v) : (v : G) ∉ ZV L V := by
  intro hz
  have he : (Submodule.Quotient.mk (Additive.ofMul v) : Vhat L V hn) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr ((mem_fixedSeed_iff L V hn _).mpr hz)
  apply hv
  rw [he, map_zero, QuadraticMap.map_zero]

theorem nonsingular_conjugation {L V : Subgroup G} [IsElementaryAbelian 2 V]
    {hn : L ≤ normalizer (V : Set G)} (D : OrthogonalMarking L V hn)
    (l : L) (v : V) : D.Nonsingular (conjugation L V hn l v) ↔ D.Nonsingular v := by
  unfold OrthogonalMarking.Nonsingular
  have he := D.equivariant l (Submodule.Quotient.mk (Additive.ofMul v))
  change D.coordinates (Submodule.Quotient.mk (Additive.ofMul (conjugation L V hn l v))) = _ at he
  rw [he]
  change BinaryPermutation.TerminalOrthogonal.Eight.form
    (BinaryPermutation.naturalRepresentation (Fin 8)
      (D.groupEquiv (QuotientGroup.mk' (conjugation L V hn).ker l)).val _) ≠ 0 ↔ _
  rw [BinaryPermutation.TerminalOrthogonal.Eight.form_invariant]

theorem Lv_le_L (L : Subgroup G) (v : G) : Lv L v ≤ L :=
  (map_subtype_le _).trans inf_le_left

theorem Lv_le_Gv (L : Subgroup G) (v : G) : Lv L v ≤ Gv v :=
  (map_subtype_le _).trans inf_le_right

theorem Kv_le_Gv (v : G) : Kv v ≤ Gv v := map_subtype_le _

theorem coreQuotientCentralizer_le_normalizer (A : Subgroup G) :
    coreQuotientCentralizer A ≤ normalizer (A : Set G) := map_subtype_le _

theorem V_le_Gv {V : Subgroup G} [IsElementaryAbelian 2 V] (v : V) : V ≤ Gv (v : G) := by
  intro x hx
  rw [Gv, mem_centralizer_singleton_iff]
  exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : V) v)

theorem Q_le_Tv {T : Sylow 2 G} {L V : Subgroup G}
    (D : Section02.ChosenModule T L V) (v : V) : Q T L ≤ Tv T (v : G) := by
  apply le_inf
  · change (LT T L).pCoreIn 2 ≤ (T : Subgroup G)
    simpa only [Sylow.coe_subtype,
      map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ LT T L from le_sup_right)] using
      pCoreIn_le_sylow (LT T L) (T.subtype (show (T : Subgroup G) ≤ LT T L from le_sup_right))
  · intro x hx
    rw [Gv, mem_centralizer_singleton_iff]
    exact (mem_centralizer_iff.mp (D.core_centralizes hx) v v.property).symm

theorem Q_le_Rv {T : Sylow 2 G} {L V : Subgroup G}
    (D : Section02.ChosenModule T L V) (v : V) : Q T L ≤ Rv T L (v : G) := by
  apply le_pCoreIn_inf (isPGroup_pCoreIn 2 (LT T L)) (pCoreIn_le 2 (LT T L))
    ((Q_le_Tv D v).trans inf_le_right)
  simpa only [pCoreIn, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
    (pCore 2 (LT T L)).le_normalizer_map (LT T L).subtype

theorem Rv_le_Gv (T : Sylow 2 G) (L : Subgroup G) (v : G) :
    Rv T L v ≤ Gv v := (pCoreIn_le 2 _).trans inf_le_right



/-- The chosen quotient has dimension six because its coordinates are an
actual linear equivalence with the natural eight-point section. -/
theorem finrank_Vhat {L V : Subgroup G} [IsElementaryAbelian 2 V]
    {hn : L ≤ normalizer (V : Set G)} (D : OrthogonalMarking L V hn) :
    Module.finrank (ZMod 2) (Vhat L V hn) = 6 :=
  D.coordinates.finrank_eq.trans BinaryPermutation.TerminalOrthogonal.Eight.finrank_natural

/-- The source's relative normality L_v ◁ M_v follows from the actual
centralizer and characteristic two-residual constructions. -/
theorem Mv_le_normalizer_Lv (L : Subgroup G) (v : G) :
    Mv L v ≤ normalizer (Lv L v : Set G) := by
  have h : Mv L v ≤ normalizer (CLv L v : Set G) :=
    (inf_le_inf le_rfl (Gv v).le_normalizer).trans inf_normalizer_le_normalizer_inf
  exact h.trans (normalizer_le_normalizer_characteristic_image
    (CLv L v) (pResidual 2 (CLv L v)))

theorem Lv_le_Mv (L : Subgroup G) (v : G) : Lv L v ≤ Mv L v :=
  le_inf ((Lv_le_L L v).trans L.le_normalizer) (Lv_le_Gv L v)

theorem Lv_normalIn_Mv (L : Subgroup G) (v : G) :
    ((Lv L v).subgroupOf (Mv L v)).Normal :=
  (normal_subgroupOf_iff_le_normalizer (Lv_le_Mv L v)).mpr (Mv_le_normalizer_Lv L v)

/-- This asserts only relative normality of the canonical candidate;
C-component membership is still the content of Lemma 12.6.3. -/
theorem Kv_normalIn_Gv (v : G) : ((Kv v).subgroupOf (Gv v)).Normal := by
  apply (normal_subgroupOf_iff_le_normalizer (Kv_le_Gv v)).mpr
  let B := (primeToResidual 3 (solvableResidual (Gv v))).map
    (solvableResidual (Gv v)).subtype
  have : B.Characteristic := inferInstance
  simpa only [Kv, B, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
    B.le_normalizer_map (Gv v).subtype

end CFSG.Quasithin.Chapter12.Section06
