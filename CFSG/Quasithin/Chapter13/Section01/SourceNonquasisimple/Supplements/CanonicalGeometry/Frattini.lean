module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.CanonicalGeometry.Invariance
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Residual.Frattini
public import Theory.GroupTheory.CComponent.SolvableSupplement
public import Theory.GroupTheory.CComponent.QuasisimpleSupplement
public import Theory.GroupTheory.SylowNormalizerFrattini

/-!
# Frattini products and comparison of the canonical residual normalizers

The original assertion that R is Sylow in O∞(LT) gives the Frattini
product for every actual supplement B. Taking solvable residuals gives
B = O∞(B) N_B(R)^∞. The canonical residual is a local C-component and
its Sylow join has two-core R. If its two-core quotient is quasisimple,
radical-supplement rigidity identifies all these residual normalizers.

The original Sylow assertion and canonical quasisimple quotient remain
explicit inputs. In particular these results do not supply the cyclic
radical quotient, its inverting involution, or faithful membership.
Source: Aschbacher--Smith 13.1.9, first proof paragraph, printed p.869.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements
open Chapter1 Chapter1.Section02 Chapter1.RadicalNormalizers
variable {G : Type*} [Group G] [Finite G]

private theorem sylow_frattini (C W R : Subgroup G)
    (hCW : C ≤ W) (hWC : W ≤ normalizer (C : Set G))
    (hs : IsSylowIn 2 R C) : C ⊔ (W ⊓ normalizer (R : Set G)) = W := by
  obtain ⟨S, hS⟩ := hs
  let C' := C.subgroupOf W
  let : C'.Normal := normal_subgroupOf_of_le_normalizer hWC
  let e : C ≃* C' := (subgroupOfEquivOfLe hCW).symm
  let S' : Sylow 2 C' := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hm : ((S' : Subgroup C').map C'.subtype).map W.subtype = R := by
    change (((S : Subgroup C).map e.toMonoidHom).map C'.subtype).map W.subtype = R
    rw [map_map, map_map]
    exact hS
  have hfr := congrArg (fun K : Subgroup W => K.map W.subtype) S'.normalizer_sup_eq_top
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, W.range_subtype] at hfr
  change _ ⊔ (C.subgroupOf W).map W.subtype = W at hfr
  rw [map_subgroupOf_eq_of_le hCW] at hfr
  apply le_antisymm (sup_le hCW inf_le_left)
  apply hfr.symm.le.trans
  apply sup_le _ le_sup_left
  apply le_trans _ le_sup_right
  apply le_inf (map_subtype_le _)
  have hh := ((S' : Subgroup C').map C'.subtype).le_normalizer_map W.subtype
  rwa [hm] at hh

/-- The Frattini factorization for an external Sylow subgroup centralizing
B modulo its radical. -/
theorem radical_normalizer_frattini {B R : Subgroup G}
    (hRB : R ≤ normalizer (B : Set G))
    (hc : ⁅B,R⁆ ≤ (solvableRadical B).map B.subtype)
    (hs : IsSylowIn 2 R ((solvableRadical B).map B.subtype ⊔ R)) :
    (solvableRadical B).map B.subtype ⊔ (B ⊓ normalizer (R : Set G)) = B := by
  let D := (solvableRadical B).map B.subtype
  let C := D ⊔ R
  let W := B ⊔ R
  have hDB : D ≤ B := map_subtype_le _
  have hWB : W ≤ normalizer (B : Set G) := sup_le B.le_normalizer hRB
  have hWD : W ≤ normalizer (D : Set G) :=
    hWB.trans (normalizer_le_normalizer_characteristic_image B (solvableRadical B))
  have hBC : B ≤ normalizer (C : Set G) := by
    apply le_normalizer_iff.mpr
    intro b hb c hc'
    have hconj : C ≤ C.comap (MulAut.conj b).toMonoidHom := by
      apply sup_le
      · intro d hd
        exact mem_sup_left (le_normalizer_iff.mp hWD b (mem_sup_left hb) d hd)
      · intro r hr
        have hcomm := hc (commutator_mem_commutator hb hr)
        have hm := C.mul_mem (mem_sup_left hcomm) (mem_sup_right hr)
        change b * r * b⁻¹ ∈ C
        simpa only [commutatorElement_def,mul_assoc,inv_mul_cancel,mul_one] using hm
    exact hconj hc'
  have hRC : R ≤ normalizer (C : Set G) :=
    (le_inf (le_sup_right.trans hWD) R.le_normalizer).trans
      (normalizer_inf_normalizer_le_normalizer_sup D R)
  have hCW : C ≤ W := sup_le (hDB.trans le_sup_left) le_sup_right
  have hfr := sylow_frattini C W R hCW (sup_le hBC hRC) hs
  apply le_antisymm (sup_le hDB inf_le_left)
  intro b hb
  have hbW : b ∈ C ⊔ (W ⊓ normalizer (R : Set G)) := hfr.symm ▸ mem_sup_left hb
  have hnC : W ⊓ normalizer (R : Set G) ≤ normalizer (C : Set G) :=
    inf_le_left.trans (sup_le hBC hRC)
  obtain ⟨c,hc',n,hn,he⟩ :=
    (coe_mul_of_right_le_normalizer_left C _ hnC).subset hbW
  obtain ⟨d,hd,r,hr,hdr⟩ :=
    (coe_mul_of_right_le_normalizer_left D R (le_sup_right.trans hWD)).subset hc'
  have hrn : r*n ∈ B := by
    have := B.mul_mem (B.inv_mem (hDB hd)) hb
    simpa only [← he,← hdr,mul_assoc,inv_mul_cancel_left] using this
  have hrnN : r*n ∈ normalizer (R : Set G) :=
    (normalizer (R : Set G)).mul_mem (R.le_normalizer hr) hn.2
  have he' : d*(r*n) = b := by
    change d*r=c at hdr
    change c*n=b at he
    rw [← mul_assoc,hdr,he]
  rw [← he']
  exact (D ⊔ (B ⊓ normalizer (R : Set G))).mul_mem (mem_sup_left hd)
    (mem_sup_right ⟨hrn,hrnN⟩)

/-- Perfectness removes the solvable quotient of the normalizer. -/
theorem radical_normalizerResidual_frattini {B R : Subgroup G} [Group.IsPerfect B]
    (hRB : R ≤ normalizer (B : Set G))
    (hc : ⁅B,R⁆ ≤ (solvableRadical B).map B.subtype)
    (hs : IsSylowIn 2 R ((solvableRadical B).map B.subtype ⊔ R)) :
    (solvableRadical B).map B.subtype ⊔ normalizerResidual B R = B := by
  have hfr := radical_normalizer_frattini hRB hc hs
  have hm := map_solvableResidual_le_sup_residual_of_sup_eq B
    ((solvableRadical B).map B.subtype) (B ⊓ normalizer (R : Set G))
    (map_subtype_le _) inf_le_left
    (B.le_normalizer.trans (normalizer_le_normalizer_characteristic_image B (solvableRadical B))) hfr
  rw [solvableResidual_eq_top, ← MonoidHom.range_eq_map, range_subtype] at hm
  exact le_antisymm (sup_le (map_subtype_le _) (normalizerResidual_le _ _)) hm

/-- The radical of L lies in the radical of its normalized Sylow join. -/
theorem radical_le_join_radical {T L : Subgroup G}
    (hTL : T ≤ normalizer (L : Set G)) :
    (solvableRadical L).map L.subtype ≤
      (solvableRadical (L ⊔ T : Subgroup G)).map (L ⊔ T).subtype := by
  let W := L ⊔ T
  let D := (solvableRadical L).map L.subtype
  have hDW : D ≤ W := (map_subtype_le _).trans le_sup_left
  have hn : W ≤ normalizer (D : Set G) :=
    (sup_le L.le_normalizer hTL).trans
      (normalizer_le_normalizer_characteristic_image L (solvableRadical L))
  let : (D.subgroupOf W).Normal := normal_subgroupOf_of_le_normalizer hn
  let : Group.IsSolvable D := Group.isSolvable_of_surjective
    (L.subtype.subgroupMap_surjective (solvableRadical L))
  let : Group.IsSolvable (D.subgroupOf W) := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe hDW).toMonoidHom) (subgroupOfEquivOfLe hDW).injective
  have hm := map_mono (f := W.subtype)
    (le_solvableRadical (D.subgroupOf W) inferInstance inferInstance)
  rwa [map_subgroupOf_eq_of_le hDW] at hm

/-- Every supplement has the Frattini product from the one original Sylow
assertion. Invariance and the radical intersections are proved here. -/
theorem supplements_frattini_of_radical_sylow {T L : Subgroup G}
    (hTL : T ≤ normalizer (L : Set G))
    (hk : (NormalizerReducedAction.componentMap L).ker = solvableRadical L)
    (hs : IsSylowIn 2 (radicalSylowCentralizer T L)
      ((solvableRadical (L ⊔ T : Subgroup G)).map (L ⊔ T).subtype))
    {B : Subgroup G} (hB : B ∈ radicalSupplements T L) :
    (solvableRadical B).map B.subtype ⊔
      normalizerResidual B (radicalSylowCentralizer T L) = B := by
  have hTB := supplement_invariant hTL hB
  have he := supplement_radicalSylowCentralizer hTL hTB hk hB.2
  have hRB : radicalSylowCentralizer T L ≤ normalizer (B : Set G) :=
    (radicalSylowCentralizer_le _ _).trans hTB
  have hc : ⁅B,radicalSylowCentralizer T L⁆ ≤ (solvableRadical B).map B.subtype := by
    rw [← he,commutator_comm]
    exact ((le_radicalSylowCentralizer_iff hTB).mp le_rfl).2
  have hd : (solvableRadical B).map B.subtype ≤
      (solvableRadical (L ⊔ T : Subgroup G)).map (L ⊔ T).subtype :=
    (supplement_radical hk hB.2).le.trans (inf_le_right.trans (radical_le_join_radical hTL))
  let := mem_L_isPerfect hB.1
  exact radical_normalizerResidual_frattini hRB hc
    (hs.restrict le_sup_right (sup_le hd (isSylowIn_iff.mp hs).2.1))

/-- The literal canonical residual itself supplements the original radical. -/
theorem canonical_frattini_of_radical_sylow {T L : Subgroup G}
    (hL : L ∈ Chapter1.L G T) (hTL : T ≤ normalizer (L : Set G))
    (hk : (NormalizerReducedAction.componentMap L).ker = solvableRadical L)
    (hs : IsSylowIn 2 (radicalSylowCentralizer T L)
      ((solvableRadical (L ⊔ T : Subgroup G)).map (L ⊔ T).subtype)) :
    (solvableRadical L).map L.subtype ⊔ canonicalSupplement T L = L :=
  supplements_frattini_of_radical_sylow hTL hk hs
    ⟨hL,sup_eq_right.mpr (map_subtype_le _)⟩

/-- Simplicity of the canonical two-core quotient identifies all the
residual normalizers; no uniqueness of maximal overgroups is used. -/
theorem supplement_residual_eq_canonical {T L B : Subgroup G}
    (hTL : T ≤ normalizer (L : Set G))
    (hk : (NormalizerReducedAction.componentMap L).ker = solvableRadical L)
    (hB : B ∈ radicalSupplements T L)
    (hfr : (solvableRadical B).map B.subtype ⊔
      normalizerResidual B (radicalSylowCentralizer T L) = B)
    (hcore : (canonicalSupplement T L).pCoreIn 2 ≤ radicalSylowCentralizer T L)
    (hq : IsQuasisimple (XiQuotient (canonicalSupplement T L))) :
    normalizerResidual B (radicalSylowCentralizer T L) = canonicalSupplement T L := by
  let R := radicalSylowCentralizer T L
  let Y := canonicalSupplement T L
  let Z := normalizerResidual B R
  let D := (solvableRadical L).map L.subtype
  have hBL : B ≤ L := hB.2 ▸ le_sup_right
  have hZY : Z ≤ Y := map_solvableResidual_mono (inf_le_inf_right _ hBL)
  have hYL : Y ≤ L := canonicalSupplement_le _ _
  have hDZ : D ⊔ Z = L := by
    apply le_antisymm (sup_le (map_subtype_le _) (hZY.trans hYL))
    have hBZ : B ≤ D ⊔ Z := by
      calc
        B = (solvableRadical B).map B.subtype ⊔ Z := hfr.symm
        _ ≤ D ⊔ Z := sup_le_sup_right
          ((supplement_radical hk hB.2).le.trans inf_le_right) Z
    exact hB.2.ge.trans (sup_le le_sup_left hBZ)
  have hDY : D ⊔ Y = L :=
    le_antisymm (sup_le (map_subtype_le _) hYL) (hDZ.ge.trans (sup_le_sup_left hZY D))
  have hrad := supplement_radical hk hDY
  have hYDZ : (Y ⊓ D) ⊔ Z = Y := by
    apply le_antisymm (sup_le inf_le_left hZY)
    intro y hy
    have hy' : y ∈ D ⊔ Z := hDZ.symm ▸ hYL hy
    have hZD : Z ≤ normalizer (D : Set G) :=
      (hZY.trans hYL).trans
        (L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (solvableRadical L)))
    obtain ⟨d,hd,z,hz,he⟩ := (coe_mul_of_right_le_normalizer_left D Z hZD).subset hy'
    have hdY : d ∈ Y := by
      have := Y.mul_mem hy (Y.inv_mem (hZY hz))
      simpa only [← he,mul_inv_cancel_right] using this
    rw [← he]
    exact ((Y ⊓ D) ⊔ Z).mul_mem (mem_sup_left ⟨hdY,hd⟩) (mem_sup_right hz)
  let := canonicalSupplement_perfect T L
  let := hq
  have hRZ : R ≤ normalizer (Z : Set G) :=
    le_normalizer_normalizerResidual
      ((radicalSylowCentralizer_le _ _).trans (supplement_invariant hTL hB)) R.le_normalizer
  have hn : pCore 2 Y ≤ normalizer (Z.subgroupOf Y : Set Y) := by
    rw [← subgroupOf_normalizer_eq hZY]
    intro x hx
    exact hRZ (hcore (mem_map_of_mem Y.subtype hx))
  have hg : solvableRadical Y ⊔ Z.subgroupOf Y = ⊤ := by
    apply map_injective Y.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hZY,hrad,
      ← MonoidHom.range_eq_map,range_subtype]
    exact hYDZ
  have hz := eq_top_of_radical_supplement_of_quasisimple_quotient
    (pCore 2 Y) (Z.subgroupOf Y) hn hg
  have hm := congrArg (map Y.subtype) hz
  simpa only [map_subgroupOf_eq_of_le hZY,← MonoidHom.range_eq_map,range_subtype] using hm


/-- The local two-core centralizes the component modulo its radical. -/
theorem join_core_le_radicalSylowCentralizer (T : Sylow 2 G) {L : Subgroup G}
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ radicalSylowCentralizer T L := by
  let W := L ⊔ (T : Subgroup G)
  let Q := W.pCoreIn 2
  have hQT : Q ≤ (T : Subgroup G) := by
    have ht := pCoreIn_le_sylow W (T.subtype le_sup_right)
    change Q ≤ ((T : Subgroup G).subgroupOf W).map W.subtype at ht
    rwa [map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ W from le_sup_right)] at ht
  have hWQ : W ≤ normalizer (Q : Set G) := W.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image W (pCore 2 W))
  have hcomm : ⁅L,Q⁆ ≤ L.pCoreIn 2 :=
    commutator_le_pCore_of_mutual_normalization L Q (isPGroup_pCoreIn 2 W)
      (le_sup_left.trans hWQ) (hQT.trans hTL)
  have hrad : L.pCoreIn 2 ≤ (solvableRadical L).map L.subtype := by
    let : Group.IsNilpotent (pCore 2 L) := pCore_isPGroup.isNilpotent
    exact map_mono (le_solvableRadical (pCore 2 L) inferInstance inferInstance)
  apply (le_radicalSylowCentralizer_iff hTL).mpr
  exact ⟨hQT,by rw [commutator_comm]; exact hcomm.trans hrad⟩

/-- The canonical join has two-core R as soon as its Frattini product
is known; inversion is needed later for its quasisimple quotient. -/
theorem canonical_join_core_of_frattini (T : Sylow 2 G) {L : Subgroup G}
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hk : (NormalizerReducedAction.componentMap L).ker = solvableRadical L)
    (hgen : (solvableRadical L).map L.subtype ⊔ canonicalSupplement T L = L) :
    (canonicalSupplement T L ⊔ (T : Subgroup G)).pCoreIn 2 =
      radicalSylowCentralizer T L := by
  have hTY := sylow_normalizes_canonicalSupplement hTL
  have he := supplement_radicalSylowCentralizer hTL hTY hk hgen
  apply le_antisymm
  · exact (join_core_le_radicalSylowCentralizer T hTY).trans_eq he
  · exact le_pCoreIn_of_normalizes
      (T.isPGroup'.to_le (radicalSylowCentralizer_le _ _))
      ((radicalSylowCentralizer_le _ _).trans le_sup_right)
      (sup_le (normalizerResidual_le_normalizer _ _)
        (sylow_normalizes_radicalSylowCentralizer hTL))

/-- The original nontrivial local two-core makes R nontrivial. -/
theorem radicalSylowCentralizer_ne_bot (T : Sylow 2 G) {L : Subgroup G}
    (hL : L ∈ Chapter1.L G (T : Subgroup G))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    radicalSylowCentralizer T L ≠ ⊥ := by
  intro he
  exact hL.2.2 (eq_bot_iff.mpr (he ▸ join_core_le_radicalSylowCentralizer T hTL))


/-- Frattini's argument lifts the local C-component property to the
canonical residual. Its local two-core is nontrivial because it contains R. -/
theorem canonical_mem_local_of_radical_sylow (T : Sylow 2 G) {L : Subgroup G}
    (hL : L ∈ Chapter1.L G (T : Subgroup G))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hs : IsSylowIn 2 (radicalSylowCentralizer T L)
      ((solvableRadical (L ⊔ (T : Subgroup G) : Subgroup G)).map
        (L ⊔ (T : Subgroup G)).subtype)) :
    canonicalSupplement T L ∈ Chapter1.L G (T : Subgroup G) := by
  let W := L ⊔ (T : Subgroup G)
  let D := (solvableRadical W).map W.subtype
  let R := radicalSylowCentralizer T L
  let N := W ⊓ normalizer (R : Set G)
  let Y := canonicalSupplement T L
  have hTR := sylow_normalizes_radicalSylowCentralizer hTL
  have hWD : W ≤ normalizer (D : Set G) := W.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image W (solvableRadical W))
  have hDN : D ⊔ N = W := sylow_frattini D W R (map_subtype_le _) hWD hs
  let : Group.IsSolvable D := Group.isSolvable_of_surjective
    (W.subtype.subgroupMap_surjective (solvableRadical W))
  let := mem_L_isPerfect hL
  let : Group.IsNilpotent (T : Subgroup G) := T.isPGroup'.isNilpotent
  have he : solvableResidual W = L.subgroupOf W := by
    apply map_injective W.subtype_injective
    rw [map_subgroupOf_eq_of_le le_sup_left]
    exact map_residual_sup_eq_of_perfect_of_solvable L (T : Subgroup G) hTL
  have hc : (solvableResidual W).IsCComponent := he.symm ▸ hL.1
  have hN := residual_isCComponent_of_solvable_supplement_in W D N
    (map_subtype_le _) inf_le_left hWD hDN hc
  have hres : Y.subgroupOf N = solvableResidual N := by
    change (normalizerResidual L R).subgroupOf N = solvableResidual N
    rw [← localNormalizer_residual_eq L (T : Subgroup G) R hL.2.1 hTL]
    exact comap_map_eq_self_of_injective N.subtype_injective _
  have hRN : R ≤ N := le_inf
    ((radicalSylowCentralizer_le _ _).trans le_sup_right) R.le_normalizer
  have hNlocal : N ∈ Chapter1.H G := by
    have hRcore : R ≤ N.pCoreIn 2 := le_pCoreIn_of_normalizes
      (T.isPGroup'.to_le (radicalSylowCentralizer_le _ _)) hRN inf_le_right
    intro hzero
    exact radicalSylowCentralizer_ne_bot T hL hTL (eq_bot_iff.mpr (hzero ▸ hRcore))
  apply mem_L_of_cComponent hNlocal
    (hL.2.1.restrict (le_inf le_sup_right hTR) inf_le_left)
    (le_inf ((canonicalSupplement_le _ _).trans le_sup_left) (normalizerResidual_le_normalizer _ _))
  exact hres.symm ▸ hN

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements
