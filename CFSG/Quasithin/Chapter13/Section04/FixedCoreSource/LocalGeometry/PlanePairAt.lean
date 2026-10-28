module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.ComponentFullSixQuotientAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Geometry.OriginalPlaneExistence

/-!
# Original plane-pair geometry from structural facts at G,T

Construct an invariant natural plane from the actual six-letter Sylow action.
The original point and plane parabolics generate the normalizer: the plane
residual fixes exactly the original fixed line, so escape makes the two
parabolics distinct in the actual A₆/S₆ quotient lattice.

Maximal two-locality then identifies both intersections in every local
overgroup of the pair. The common Sylow and literal residual maps identify
the relative fixed-line centralizers, relative normality and O^{3'} clause
of 13.4.7(c). ComponentSixPairAt supplies the actual nonsolvable application.
These specialize the proved Solvable/Geometry arguments; only structural
facts at the original G,T are used. The earlier sources remain explicit.
Source: Aschbacher--Smith 13.4.7(c), 13.4.9 and 13.4.10(8), pp.899,906,909.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Nonsolvable Solvable BinaryPermutation
open Section08.TransvectionRecognition.Component.ModelExtension
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
private theorem normalizes_preimage_of_permutation
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hn : normalizer (L : Set G) ≤ normalizer (V : Set G))
    (q : normalizer (L : Set G) →* Equiv.Perm (Fin 6))
    (hq : ∀ (x : normalizer (L : Set G)) (v : V),
      (m.coordinate (V.normalizerMonoidHom (inclusion hn x) v)).toAdd =
        coreRepresentation (Fin 6) (q x) (m.coordinate v).toAdd)
    (W : Submodule (ZMod 2) (natural (Fin 6)))
    (x : normalizer (L : Set G)) (hx : q x ∈ flagStabilizer W) :
    x.val ∈ normalizer (m.naturalPreimage W : Set G) := by
  have he (v : V) :
      coreToNatural (Fin 6) (m.coordinate (V.normalizerMonoidHom (inclusion hn x) v)).toAdd =
        naturalRepresentation (Fin 6) (q x) (coreToNatural (Fin 6) (m.coordinate v).toAdd) := by
    rw [hq,coreToNatural_equivariant]
  apply mem_normalizer_iff.mpr
  intro a
  by_cases ha : a ∈ V
  · let v : V := ⟨a,ha⟩
    have hh := hx (coreToNatural (Fin 6) (m.coordinate v).toAdd)
    rw [←he,←m.mem_naturalPreimage,←m.mem_naturalPreimage] at hh
    exact hh.symm
  · have ha' : x.val * a * x.val⁻¹ ∉ V :=
      fun hh => ha (((mem_normalizer_iff.mp (hn x.property)) a).mpr hh)
    exact iff_of_false (fun hh => ha (m.naturalPreimage_le W hh))
      (fun hh => ha' (m.naturalPreimage_le W hh))

/-- Construct the source plane from the actual normalizer action and the
original Sylow subgroup, without an assumed invariant subspace. -/
theorem exists_original_invariant_plane_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D) :
    ∃ W : Submodule (ZMod 2) (natural (Fin 6)),
      Module.finrank (ZMod 2) W = 2 ∧
        (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G) := by
  have hn := normalizer_component_le_module_at h structural D m
  obtain ⟨q,hq,hqL,_⟩ := Nonsolvable.exists_core_normalizer_permutation D m hn
  have hA : alternatingGroup (Fin 6) ≤ q.range := by
    intro a ha
    obtain ⟨v,hv⟩ := m.quotient.surjective ⟨a,ha⟩
    obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (centralCore L) v
    exact ⟨inclusion L.le_normalizer l,(hqL l).trans (congrArg Subtype.val hv)⟩
  let S := T.subtype D.sylow_normalizes_component
  let Q := S.mapSurjective q.rangeRestrict_surjective
  obtain ⟨g,hg⟩ := sylow_flag_exists q.range hA Q
  let W := move g.val canonicalPlane
  refine ⟨W,(move_finrank _ _).trans
    canonicalPlane_finrank,?_⟩
  intro t ht
  let x : normalizer (L : Set G) := ⟨t,D.sylow_normalizes_component ht⟩
  have hx : q x ∈ (Q : Subgroup q.range).map q.range.subtype :=
    ⟨q.rangeRestrict x,⟨x,ht,rfl⟩,rfl⟩
  apply normalizes_preimage_of_permutation D m hn q hq W x
  exact (Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing.mem_stabilizer_iff_map W _).mpr
    (hg _ hx).2

theorem normalizer_quotient_of_ordinary_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G)) :
    Nonempty ((normalizer (L : Set G) ⧸ pCore 2 (normalizer (L : Set G))) ≃*
      alternatingGroup (Fin 6)) ∨
    Nonempty ((normalizer (L : Set G) ⧸ pCore 2 (normalizer (L : Set G))) ≃*
      Equiv.Perm (Fin 6)) := by
  rw [hM]
  obtain ⟨q,_,_,him,hker⟩ := exists_core_product_permutation_at D m h structural eL
  have hA : alternatingGroup (Fin 6) ≤ q.range := him ▸ (L.subgroupOf _).map_le_range q
  have hd := index_dvd_of_le hA
  rw [alternatingGroup.index_eq_two] at hd
  let eq : ((L ⊔ (T : Subgroup G) : Subgroup G) ⧸ pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) ≃* q.range :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivRange q)
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with hi | hi
  · exact Or.inr ⟨eq.trans ((MulEquiv.subgroupCongr (index_eq_one.mp hi)).trans topEquiv)⟩
  · exact Or.inl ⟨eq.trans (MulEquiv.subgroupCongr
      (Equiv.Perm.eq_alternatingGroup_of_index_eq_two hi))⟩

/-- The six-letter action of the full normalizer has the same orbits on V
as L. Lifting the matching even permutation gives the centralizer supplement. -/
theorem normalizer_component_centralizer_supplement_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D) (z : V) :
    normalizer (L : Set G) =
      L ⊔ (centralizer ({z.val} : Set G) ⊓ normalizer (L : Set G)) := by
  have hn := normalizer_component_le_module_at h structural D m
  obtain ⟨q,hq,_,_⟩ := Nonsolvable.exists_core_normalizer_permutation D m hn
  apply le_antisymm ?_ (sup_le L.le_normalizer inf_le_right)
  intro x hx
  let a : normalizer (L : Set G) := ⟨x,hx⟩
  let w := (m.coordinate z).toAdd
  obtain ⟨b,hb⟩ := BinaryPermutation.exists_even_permutation_of_weight
    (by decide : 3 ≤ Fintype.card (Fin 6)) w.val
    (BinaryPermutation.representation (Fin 6) (q a) w.val)
    (BinaryPermutation.wordWeight_permute (q a) w.val).symm
  obtain ⟨v,hv⟩ := m.quotient.surjective b
  obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (centralCore L) v
  have he : l.val * z.val * l.val⁻¹ = x * z.val * x⁻¹ := by
    have he := m.equivariant l z
    rw [hv] at he
    have hqz := hq a z
    have hb' : BinaryPermutation.coreRepresentation (Fin 6) b.val w =
        BinaryPermutation.coreRepresentation (Fin 6) (q a) w := Subtype.ext hb
    have hh := he.trans (hb'.trans hqz.symm)
    exact congrArg Subtype.val (m.coordinate.injective (Multiplicative.toAdd.injective hh))
  have hc : l.val⁻¹ * x ∈ centralizer ({z.val} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    have hh := congrArg (fun y : G => l.val⁻¹ * y * x) he
    simpa only [mul_assoc,inv_mul_cancel_left,mul_inv_cancel_left,inv_mul_cancel,mul_one] using hh.symm
  have hm : l.val⁻¹ * x ∈ normalizer (L : Set G) :=
    (normalizer (L : Set G)).mul_mem
      ((normalizer (L : Set G)).inv_mem (L.le_normalizer l.property)) hx
  have hh := (L ⊔ (centralizer ({z.val} : Set G) ⊓ normalizer (L : Set G))).mul_mem
    (mem_sup_left l.property) (mem_sup_right ⟨hc,hm⟩)
  simpa only [mul_inv_cancel_left] using hh


/-- The two original inside parabolics generate LT. Distinctness follows
from the plane residual's fixed line and the chosen escaping vector. -/
theorem original_inside_parabolics_generate_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hinter : centralizer ({z.val} : Set G) ⊓ normalizer (L : Set G) =
      firstCentralizerResidual L z.val ⊔ (T : Subgroup G))
    (W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)))
    (hW : Module.finrank (ZMod 2) W = 2)
    (hT : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G)) :
    normalizer (L : Set G) = L ⊔ (T : Subgroup G) ∧
      (firstCentralizerResidual L z.val ⊔ (T : Subgroup G)) ⊔
        ((L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)) =
          L ⊔ (T : Subgroup G) := by
  have hM := normalizer_eq_component_sylow_of_centralizer_intersection
    (normalizer_component_centralizer_supplement_at h structural D m z) hinter
  let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)
  have hBM : B ≤ normalizer (L : Set G) := by rw [hM]; exact inf_le_left
  have hTB : (T : Subgroup G) ≤ B := le_inf le_sup_right hT
  obtain ⟨⟨eB⟩,_,_,_⟩ := original_second_flag_chief_factors D m eL W hW hT
  have hB : IsCoatom (B.subgroupOf (normalizer (L : Set G))) := by
    rw [hM]
    exact original_second_flag_coatom D m W hW hT
  let M := normalizer (L : Set G)
  let A := centralizer ({z.val} : Set G) ⊓ M
  let Ai := (centralizer ({z.val} : Set G)).subgroupOf M
  let Bi := B.subgroupOf M
  let S := T.subtype D.sylow_normalizes_component
  have hTA : (T : Subgroup G) ≤ A :=
    le_inf (original_sylow_le_centralizer hz) D.sylow_normalizes_component
  have hcore : IsPGroup 2 (centralCore L) := by
    rw [centralCore_eq_twoCore_of_ordinary eL]
    exact pCore_isPGroup
  obtain ⟨eA⟩ := normalizer_centralizer_quotient D m hcore z hzL hinter
  let a : Ai ≃* A :=
    (MulEquiv.subgroupCongr (inf_subgroupOf_right _ _).symm).trans
      (subgroupOfEquivOfLe (show A ≤ M from inf_le_right))
  have ha : ¬ IsPGroup 2 Ai := fun hp =>
    not_twoGroup_of_symmetricThree_quotient eA (hp.of_equiv a)
  let b := subgroupOfEquivOfLe hBM
  have hb : ¬ IsPGroup 2 Bi := fun hp =>
    not_twoGroup_of_symmetricThree_quotient eB (hp.of_equiv b)
  have hSA : (S : Subgroup M) ≤ Ai := fun _ hx => (hTA hx).1
  have hSB : (S : Subgroup M) ≤ Bi := fun _ hx => hTB hx
  have hAp : Ai ≠ ⊤ := by
    intro he
    apply hzL
    intro l hl
    exact mem_centralizer_singleton_iff.mp
      (show (⟨l,L.le_normalizer hl⟩ : M) ∈ Ai from he ▸ mem_top _)
  have hne : Ai ≠ Bi := by
    intro he
    have hBC : B ≤ centralizer ({z.val} : Set G) := by
      intro b hb
      exact (show (⟨b,hBM hb⟩ : M) ∈ Ai from he ▸ hb)
    have hzK : z.val ∈ V ⊓ centralizer (((pResidual 2 B).map B.subtype : Subgroup G) : Set G) := by
      refine ⟨z.property,?_⟩
      intro k hk
      exact mem_centralizer_singleton_iff.mp (hBC ((map_subtype_le _) hk))
    rw [original_second_flag_fixed D m W hW hT] at hzK
    exact hzL hzK.2
  have hp := Quasithin.I5.RankTwoParabolics.of_six_letter_two_quotient (pCore 2 M) pCore_isPGroup
    (normalizer_quotient_of_ordinary_at h structural D m eL hM) S Ai Bi
    (lt_iff_le_not_ge.mpr ⟨hSA,fun hh => ha (S.isPGroup'.to_le hh)⟩)
    (lt_iff_le_not_ge.mpr ⟨hSB,fun hh => hb (S.isPGroup'.to_le hh)⟩)
    hAp hB.ne_top hne
  have hg := congrArg (map M.subtype) hp.generate
  rw [Subgroup.map_sup,subgroupOf_map_subtype,map_subgroupOf_eq_of_le hBM,
    ←MonoidHom.range_eq_map,range_subtype] at hg
  rw [hinter] at hg
  exact ⟨hM,hg.trans hM⟩

/-- The fixed line lies in the center of the original Sylow subgroup. -/
theorem fixed_le_original_omegaCenter_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D) :
    V ⊓ centralizer (L : Set G) ≤ omegaOneCenterAmbient (T : Subgroup G) := by
  let := D.elementary
  intro d hd
  apply (mem_omegaOneCenterAmbient_iff _ _).mpr
  refine ⟨D.le_sylow hd.1, elemPow_eq_one_of_isElementaryAbelian d hd.1, ?_⟩
  intro t ht
  exact (mem_centralizer_iff.mp
    (normalizer_component_le_fixed_centralizer_at h structural D m
      (D.sylow_normalizes_component ht)) d hd).symm

omit [Finite G] in
private theorem local_overgroup_le_maximal (M X : Subgroup G)
    (hM : IsMaximalTwoLocal M) (hX : X ∈ Chapter1.H G) (hMX : M ≤ X) : X ≤ M := by
  have hn : X ≤ normalizer (X.pCoreIn 2 : Set G) := by
    simpa only [pCoreIn,normalizer_eq_top,← MonoidHom.range_eq_map,range_subtype] using
      (pCore 2 X).le_normalizer_map X.subtype
  exact hn.trans (hM.2 ⟨X.pCoreIn 2,hX,isPGroup_pCoreIn 2 X,rfl⟩ (hMX.trans hn))

/-- The two literal intersections in every local overgroup of the source
amalgam. The assumption on X is exactly the conditional premise of13.4.7(c). -/
theorem amalgam_intersections_in_local_overgroup_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (z : G) (P B X : Subgroup G)
    (hPH : P ≤ centralizer ({z} : Set G))
    (hPmax : IsCoatom (P.subgroupOf (centralizer ({z} : Set G))))
    (hPM : ¬ P ≤ normalizer (L : Set G))
    (hBM : B ≤ normalizer (L : Set G))
    (hBmax : IsCoatom (B.subgroupOf (normalizer (L : Set G))))
    (hgen : (centralizer ({z} : Set G) ⊓ normalizer (L : Set G)) ⊔ B =
      normalizer (L : Set G))
    (hX : X ∈ Chapter1.H G) (hPX : P ≤ X) (hBX : B ≤ X) :
    X ⊓ normalizer (L : Set G) = B ∧ X ⊓ centralizer ({z} : Set G) = P := by
  let M := normalizer (L : Set G)
  let H := centralizer ({z} : Set G)
  have hmax : IsMaximalTwoLocal M :=
    (h.source_normalizer_maximal_unique_at structural
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)).1
  have hMX : ¬ M ≤ X := fun hh => hPM (hPX.trans
    (local_overgroup_le_maximal M X hmax hX hh))
  have hXM : X.subgroupOf M ≠ ⊤ := by
    intro he
    apply hMX
    intro x hx
    exact (show (⟨x,hx⟩ : M) ∈ X.subgroupOf M from he ▸ mem_top _)
  have hb := (hBmax.le_iff_eq hXM).mp (subgroupOf_mono M hBX)
  have hXB : X ⊓ M = B := by
    have hh := congrArg (map M.subtype) hb
    rwa [subgroupOf_map_subtype,map_subgroupOf_eq_of_le hBM] at hh
  have hHX : ¬ H ≤ X := by
    intro hh
    apply hMX
    change normalizer (L : Set G) ≤ X
    rw [←hgen]
    exact sup_le (inf_le_left.trans hh) hBX
  have hXH : X.subgroupOf H ≠ ⊤ := by
    intro he
    apply hHX
    intro x hx
    exact (show (⟨x,hx⟩ : H) ∈ X.subgroupOf H from he ▸ mem_top _)
  have hp := (hPmax.le_iff_eq hXH).mp (subgroupOf_mono H hPX)
  refine ⟨hXB,?_⟩
  have hh := congrArg (map H.subtype) hp
  rwa [subgroupOf_map_subtype,map_subgroupOf_eq_of_le hPH] at hh

/-- Both relative normality clauses and the prime-to-three residual clause
in13.4.7(c), using the original fixed line for the inside parabolic. -/
theorem amalgam_residual_centralizers_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (z : G) (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G))
    (P B X : Subgroup G) (hTP : (T : Subgroup G) ≤ P)
    (hPH : P ≤ centralizer ({z} : Set G))
    (hPmax : IsCoatom (P.subgroupOf (centralizer ({z} : Set G))))
    (hPM : ¬ P ≤ normalizer (L : Set G))
    (eP : (P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3))
    (hBM : B ≤ normalizer (L : Set G))
    (hBmax : IsCoatom (B.subgroupOf (normalizer (L : Set G))))
    (hgen : (centralizer ({z} : Set G) ⊓ normalizer (L : Set G)) ⊔ B =
      normalizer (L : Set G))
    (hfixed : centralizer ((omegaOneCenterAmbient (T : Subgroup G) ⊓
      centralizer ((pResidual 2 B).map B.subtype : Set G) : Subgroup G) : Set G) =
        normalizer (L : Set G))
    (hX : X ∈ Chapter1.H G) (hPX : P ≤ X) (hBX : B ≤ X) :
    let K₁ := (pResidual 2 P).map P.subtype
    let K₂ := (pResidual 2 B).map B.subtype
    let C₁ := X ⊓ centralizer ((omegaOneCenterAmbient (T : Subgroup G) ⊓
      centralizer (K₁ : Set G) : Subgroup G) : Set G)
    let C₂ := X ⊓ centralizer ((omegaOneCenterAmbient (T : Subgroup G) ⊓
      centralizer (K₂ : Set G) : Subgroup G) : Set G)
    X ⊓ normalizer (L : Set G) = B ∧ X ⊓ centralizer ({z} : Set G) = P ∧
      C₁ = P ∧ C₂ = B ∧ (K₁.subgroupOf C₁).Normal ∧ (K₂.subgroupOf C₂).Normal ∧
      (primeToResidual 3 C₁).map C₁.subtype = K₁ := by
  obtain ⟨hXM,hXH⟩ := amalgam_intersections_in_local_overgroup_at h structural z P B X
    hPH hPmax hPM hBM hBmax hgen hX hPX hBX
  obtain ⟨hC₁,hn₁,hr⟩ := residual_fixed_cubic_centralizer_of_intersection z hz P X
    hTP hPX hPH hXH eP
  have hC₂ : X ⊓ centralizer ((omegaOneCenterAmbient (T : Subgroup G) ⊓
      centralizer ((pResidual 2 B).map B.subtype : Set G) : Subgroup G) : Set G) = B := by
    rw [hfixed]
    exact hXM
  refine ⟨hXM,hXH,hC₁,hC₂,hn₁,?_,hr⟩
  rw [hC₂]
  apply (normal_subgroupOf_iff_le_normalizer (map_subtype_le _)).mpr
  simpa only [normalizer_eq_top,← MonoidHom.range_eq_map,range_subtype] using
    (pResidual 2 B).le_normalizer_map B.subtype


end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
