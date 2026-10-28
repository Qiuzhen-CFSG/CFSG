module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.CubicOrbit.Paired
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.Noncentral.Model
public import Theory.GroupTheory.PerfectSimpleImageOrder

/-!
# Noncentrality of the cubic critical-plane orbit

The whole natural-or-augmentation cover controls displacement into the
literal critical plane. If its normal orbit were fixed modulo the base
Z-layer, the opposite-core intersection would generate a normal subgroup
centralizing the plane. Its displacement then detects the whole component,
forcing the intrinsic core into Z and contradicting the cubic kernel.

The normal-generation argument retains E/Q of order three. Perfectness
removes a normal Q supplement only after an escaping two-subgroup has
excluded the E alternative. Every coordinate map uses the specified common
edge; X, Z, and the whole moved cover remain distinct. Selection constructs
the actual favorable pair and applies this noncentrality to its quotient.
Source: Meierfrankenfeld--Stellmacher (1993), (3.6), printed p.871.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation BinaryPermutation
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.CubicAction
open Natural.Exhaustion.DistanceTwo.Geometry
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "K" => L.subgroupOf (L ⊔ R)
local notation "T" => edge L R
local notation "W" => (⁅centralOmega L R,K⁆ : Subgroup M)
local notation "π" => projection h e hz hk

include h e hz in
/-- An escaping two-subgroup detects the component in an arbitrary normal subgroup.
The normal subgroup need not contain Q; perfectness removes its Q supplement. -/
theorem component_le_normal_of_escaping_two
    (N A : Subgroup M) [N.Normal] (hA : IsPGroup 2 A)
    (hAQ : ¬ A ≤ pCore 2 M) (hAN : A ≤ N) : K ≤ N := by
  let := h.component_perfect
  let f := subgroupOfEquivOfLe (show L ≤ L ⊔ R from le_sup_left)
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := f.symm.toMonoidHom) f.symm.surjective
  apply perfect_le_of_le_sup_two K N (pCore 2 M) pCore_isPGroup
  exact component_le_normal_of_two_subgroup h e hz (N ⊔ pCore 2 M) A
    le_sup_right hA hAQ (hAN.trans le_sup_left)

include h e hz in
/-- The same escaping actor detects component movement on every normal section. -/
theorem normal_commutator_le_of_escaping_two
    (D N A : Subgroup M) [D.Normal] [N.Normal] (hA : IsPGroup 2 A)
    (hAQ : ¬ A ≤ pCore 2 M) (hcomm : ⁅D,A⁆ ≤ N) : ⁅D,K⁆ ≤ N := by
  let q := QuotientGroup.mk' N
  let C := (centralizer (D.map q : Set (M ⧸ N))).comap q
  let : (D.map q).Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective N)
  have hc (B : Subgroup M) : B ≤ C ↔ ⁅D,B⁆ ≤ N := by
    change B ≤ (centralizer (D.map q : Set (M ⧸ N))).comap q ↔ _
    rw [←map_le_iff_le_comap,←le_centralizer_iff,
      ←commutator_eq_bot_iff_le_centralizer,←map_commutator,
      Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk']
  exact (hc K).mp (component_le_normal_of_escaping_two h e hz C A hA hAQ
    ((hc A).mpr hcomm))

include h in
/-- Coordinates at a specified incident edge, retaining its original two-core,
whole moved cover and central edge attachment. -/
theorem vertex_moved_coordinates {c b : Vertex T}
    (hc : color T c = false) (hcb : Adjacent T c b) :
    ∃ i : M →* FreeAmalgam T, Function.Injective i ∧
      i.range = stabilizer T c ∧ (pCore 2 M).map i = Q T c ∧
      (W).map i = ⁅X T c,Ltilde T c⁆ ∧
      (omegaCenter T).map i = Z T b ∧ (T).map i = Q T b := by
  obtain ⟨g,hg | hg⟩ := (adjacent_iff_exists_common T c b).mp hcb
  · rcases hg with ⟨rfl,rfl⟩
    let i := (MulAut.conj g⁻¹).toMonoidHom.comp (embedM T)
    have hga : act T g (alpha T) = mVertex T g := by simp [alpha]
    have hgb : act T g (beta T) = hVertex T g := by simp [beta]
    refine ⟨i,(MulAut.conj g⁻¹).injective.comp (embedM_injective T),?_,?_,?_,?_,?_⟩
    · rw [MonoidHom.range_comp]
      change (Mbar T).map _ = _
      rw [←stabilizer_m_base,←stabilizer_act]
      simp only [act_mVertex,one_mul]
    · rw [←map_map,←Q_alpha T h.relative_radical.isPGroup h.relative_radical.twoCore_le,
        ←Q_act,hga]
    · rw [←map_map,map_commutator,←graph_X h,←graph_component h,
        map_commutator,←X_act,←Ltilde_act,hga]
    · have he : (omegaCenter T).map (embedM T) = Z T (beta T) := by
        rw [Z,if_neg (by exact Bool.noConfusion : color T (beta T) ≠ false),edgeOmega,Q_beta,
          omegaCenter_map _ _ (embedM_injective T)]
      rw [←map_map,he,←Z_act,hgb]
    · rw [←map_map,←Q_beta,←Q_act,hgb]
  · rw [hg.1] at hc
    cases hc

include h e hz in
/-- The opposite layer is the actual whole moved cover joined with its edge seed. -/
theorem vertex_Z_eq_moved_sup_edge {c b : Vertex T}
    (hc : color T c = false) (hcb : Adjacent T c b) :
    Z T c = ⁅X T c,Ltilde T c⁆ ⊔ Z T b := by
  obtain ⟨g,hg | hg⟩ := (adjacent_iff_exists_common T c b).mp hcb
  · rcases hg with ⟨rfl,rfl⟩
    have he := congrArg (fun A : Subgroup (FreeAmalgam T) =>
      A.map (MulAut.conj g⁻¹).toMonoidHom)
      (graph_Z_eq_moved_sup_edge h e hz (base_adjacent T))
    have hmove : (W).map (embedM T) = ⁅X T (alpha T),Ltilde T (alpha T)⁆ := by
      rw [graph_X h,graph_component h,map_commutator]
    rw [hmove] at he
    rw [Subgroup.map_sup,map_commutator,
      ←Z_act,←X_act,←Ltilde_act,←Z_act] at he
    simpa [alpha,beta] using he
  · rw [hg.1] at hc
    cases hc
private theorem plane_normalized_edge
    {M₀ : Type*} [Group M₀] [Finite M₀] {R : Subgroup M₀} (geo : Geometry R) (hb : geo.b R = 2)
    {c t : Vertex R}
    (hc : CriticalPair R (alpha R) c (geo.exists_critical (alpha R) rfl))
    (hat : Adjacent R (alpha R) t) (hct : Adjacent R c t) :
    Q R t ≤ normalizer (criticalPlane R c t : Set (FreeAmalgam R)) := by
  have htGa : Q R t ≤ stabilizer R (alpha R) :=
    fun k hk => hk.2 (alpha R) (adjacent_symm R hat)
  have htGc : Q R t ≤ stabilizer R c :=
    fun k hk => hk.2 c (adjacent_symm R hct)
  apply le_normalizer_iff.mpr
  intro k hk y hy
  apply (mem_criticalPlane_iff geo hb hc hat hct _).mpr
  have hy' := (mem_criticalPlane_iff geo hb hc hat hct y).mp hy
  refine ⟨le_normalizer_iff.mp (Z_normalized R c) k (htGc hk) y hy'.1,?_⟩
  intro q hq
  have hq' : k⁻¹*q*k ∈ Q R (alpha R) := by
    simpa only [inv_inv] using
      le_normalizer_iff.mp (Q_normalized R (alpha R)) k⁻¹
        (htGa ((Q R t).inv_mem hk)) q hq
  have hm := hy'.2 (k⁻¹*q*k) hq'
  have hconj : (MulAut.conj k) ⁅k⁻¹*q*k,y⁆ ∈ Z R t :=
    le_normalizer_iff.mp (Z_normalized R t) k hk.1 _ hm
  rw [map_commutatorElement] at hconj
  have he : (MulAut.conj k) (k⁻¹*q*k) = q := by
    simp [MulAut.conj_apply,mul_assoc]
  rw [he] at hconj
  exact hconj



include h e hz hk in
/-- A subgroup of Q centralizing the actual critical plane sends the whole
opposite layer into that plane, with the cubic action kernel retained. -/
theorem critical_plane_centralizer_displacement
    (hb : sourceDistance h = 2) {c b : Vertex T}
    (hc : CriticalPair T (alpha T) c ((sourceGeometry h).exists_critical _ rfl))
    (hab : Adjacent T (alpha T) b) (hcb : Adjacent T c b)
    (N : Subgroup (FreeAmalgam T)) (hN : N ≤ Q T (alpha T))
    (hfix : N ≤ centralizer (criticalPlane T c b : Set (FreeAmalgam T))) :
    ⁅N,Z T c⁆ ≤ criticalPlane T c b := by
  obtain ⟨i,hi,hiG,hiQ,hiW,hiS,hiR⟩ := vertex_moved_coordinates h
    (critical_endpoint_color T (alpha T) rfl _ hc) hcb
  let := h.relative_normal
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le (commutator_le_left (centralOmega L R) K)
  let q := π
  let B := (T).map q
  have hq := projection_surjective_of_distanceTwo h e hz hk hb
  let hker := moved_projection_kernel h e hz hk
  let ρ := NormalElementaryQuotient.representation W q hq hker
  have hmodel := moved_subgroup_cover_model h e hz hk hb
  have hZc : Z T c = (W ⊔ omegaCenter T).map i := by
    rw [Subgroup.map_sup,hiW,hiS]
    exact vertex_Z_eq_moved_sup_edge h e hz
      (critical_endpoint_color T (alpha T) rfl _ hc) hcb
  have hQa : Q T (alpha T) ≤ (T).map i := by
    rw [hiR]
    exact Q_le_adjacent_h T (DistanceTwo.NaturalCore.edge_color hab) hab
  have hWR : W ≤ T := (commutator_le_left (centralOmega L R) K).trans
    ((omegaCenter_le _).trans (h.relative_radical.twoCore_le))
  let P : Additive W → Prop := fun v => i v.toMul.val ∈ criticalPlane T c b
  have hP (v : Additive W) (hv : Noncentral.SecondFixed ρ B v) : P v := by
    apply (mem_criticalPlane_iff (sourceGeometry h) hb hc hab hcb _).mpr
    refine ⟨?_,?_⟩
    · rw [hZc]
      exact mem_map_of_mem i (show v.toMul.val ∈ W ⊔ omegaCenter T from
        mem_sup_left v.toMul.property)
    · intro y hy
      obtain ⟨y,hyR,rfl⟩ := hQa hy
      let δ := ρ (q y) v-v
      have he : δ.toMul.val = ⁅y,v.toMul.val⁆ := by
        dsimp only [δ]
        rw [toMul_sub,div_eq_mul_inv]
        change ((ρ (q y) v).toMul : M) * v.toMul.val⁻¹ = _
        rw [NormalElementaryQuotient.representation_apply]
        rfl
      have hδ : δ.toMul.val ∈ omegaCenter T := by
        apply mem_omegaCenter_iff.mpr
        refine ⟨hWR δ.toMul.property,
          elemPow_eq_one_of_isElementaryAbelian (p := 2) _ δ.toMul.property,?_⟩
        intro r hr
        have heq := congrArg (fun x : Additive W => x.toMul.val)
          (hv (q y) (mem_map_of_mem q hyR) (q r) (mem_map_of_mem q hr))
        rw [NormalElementaryQuotient.representation_apply] at heq
        exact mul_inv_eq_iff_eq_mul.mp heq
      rw [←map_commutatorElement,←he,←hiS]
      exact mem_map_of_mem i hδ
  apply commutator_le.mpr
  intro n hnN z hzZ
  obtain ⟨n,hnR,rfl⟩ := hQa (hN hnN)
  obtain ⟨z,hz,rfl⟩ := hZc.le hzZ
  obtain ⟨w,hw,s,hs,rfl⟩ := mem_sup_of_normal_left.mp hz
  have hnf (v : Additive W) (hv : P v) : ρ (q n) v = v := by
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [NormalElementaryQuotient.representation_apply]
    apply mul_inv_eq_iff_eq_mul.mpr
    apply hi
    simp only [map_mul]
    exact (hfix hnN _ hv).symm
  let w0 : Additive W := Additive.ofMul ⟨w,hw⟩
  have hm := Noncentral.cover_displacement_of_second_fixed ρ hmodel B
    ((h.relative_radical.isPGroup).map q) P hP (q n) (mem_map_of_mem q hnR) hnf w0
  have he : (ρ (q n) w0-w0).toMul.val = ⁅n,w⁆ := by
    rw [toMul_sub,div_eq_mul_inv]
    change ((ρ (q n) w0).toMul : M) * w⁻¹ = _
    rw [NormalElementaryQuotient.representation_apply]
    rfl
  change i (ρ (q n) w0-w0).toMul.val ∈ criticalPlane T c b at hm
  rw [he,map_commutatorElement] at hm
  have hns : Commute (i n) (i s) := by
    change i n * i s = i s * i n
    simpa only [map_mul] using congrArg i ((mem_omegaCenter_iff.mp hs).2.2 n hnR)
  rw [map_mul,commutatorElement_mul_right_eq_mul_conj,hns.commutator_eq]
  simpa only [mul_one,mul_inv_cancel_right] using hm

include h e hz in
private theorem normal_orbit_noncentral
    (S Z0 E Y : Subgroup M) [Z0.Normal] [IsMulCommutative E]
    (hEp : IsPGroup 2 E)
    (hgen : K ⊔ S = ⊤)
    (hTY : S ≤ normalizer (Y : Set M))
    (hYE : Y ≤ E)
    (hZQ : Z0 ≤ centralizer (pCore 2 M : Set M))
    (hE : ¬ E ≤ pCore 2 M)
    (hQE : ⁅pCore 2 M,E⁆ ≤ E ⊓ pCore 2 M)
    (hlarge : ¬ ⁅pCore 2 M,K⁆ ≤ Z0)
    (hdisplacement : ∀ (N : Subgroup M) [N.Normal],
      N ≤ pCore 2 M → N ≤ centralizer (Y : Set M) → ⁅N,E⁆ ≤ Y) :
    ¬ ⁅normalClosure (Y : Set M),K⁆ ≤ Z0 := by
  let := h.relative_normal
  intro hcentral
  let A := normalClosure (Y : Set M)
  have hKY : K ≤ normalizer ((Y ⊔ Z0 : Subgroup M) : Set M) := by
    apply le_normalizer_iff_commutator_le_right.mpr
    have hKYZ : ⁅K,Y ⊔ Z0⁆ ≤ Z0 := by
      apply commutator_le.mpr
      intro k hk x hx
      obtain ⟨y,hy,z,hz,rfl⟩ := mem_sup_of_normal_right.mp hx
      rw [commutatorElement_mul_right_eq_mul_conj]
      have hky : ⁅k,y⁆ ∈ Z0 := by
        rw [commutator_comm] at hcentral
        exact hcentral (commutator_mem_commutator hk (le_normalClosure hy))
      have hcz := (inferInstance : Z0.Normal).conj_mem _
        (commutator_le_right (K) Z0 (commutator_mem_commutator hk hz)) y
      simpa only [mul_assoc] using Z0.mul_mem hky hcz
    exact hKYZ.trans le_sup_right
  have hTZ : S ≤ normalizer ((Y ⊔ Z0 : Subgroup M) : Set M) :=
    (le_inf hTY le_normalizer_of_normal).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  let : (Y ⊔ Z0).Normal := normalizer_eq_top_iff.mp
    (top_unique (hgen ▸ sup_le hKY hTZ))
  have hA : A ≤ Y ⊔ Z0 := normalClosure_le_normal (show Y ≤ Y ⊔ Z0 from le_sup_left)
  let N := normalClosure ((E ⊓ pCore 2 M : Subgroup M) : Set M)
  have hNQ : N ≤ pCore 2 M := normalClosure_le_normal (show E ⊓ pCore 2 M ≤ _ from inf_le_right)
  have hIC : E ⊓ pCore 2 M ≤ centralizer (A : Set M) := by
    apply le_centralizer_iff.mp
    apply hA.trans
    apply sup_le
    · intro y hy x hx
      exact congrArg Subtype.val (mul_comm (⟨x,hx.1⟩ : E) ⟨y,hYE hy⟩)
    · exact hZQ.trans (centralizer_le (show E ⊓ pCore 2 M ≤ _ from inf_le_right))
  have hNC : N ≤ centralizer (A : Set M) := normalClosure_le_normal hIC
  have hNE : ⁅N,E⁆ ≤ A := (hdisplacement N hNQ
    (hNC.trans (centralizer_le le_normalClosure))).trans le_normalClosure
  have hNK : ⁅N,K⁆ ≤ A := normal_commutator_le_of_escaping_two h e hz N A E hEp hE hNE
  have hKN : ⁅pCore 2 M,K⁆ ≤ N :=
    normal_commutator_le_of_escaping_two h e hz (pCore 2 M) N E hEp hE (hQE.trans le_normalClosure)
  have hpN : IsPGroup 2 N := (pCore_isPGroup (p := 2) (G := M)).of_injective
    (inclusion hNQ) (inclusion_injective _)
  have hidN : ⁅⁅N,K⁆,K⁆ = ⁅N,K⁆ :=
    commutator_isPPerfect_idempotent (K) N
      h.relative_twoPerfect hpN le_normalizer_of_normal
  have hidQ : ⁅⁅pCore 2 M,K⁆,K⁆ =
      ⁅pCore 2 M,K⁆ := commutator_isPPerfect_idempotent
        (K) (pCore 2 M) h.relative_twoPerfect pCore_isPGroup le_normalizer_of_normal
  apply hlarge
  calc
    ⁅pCore 2 M,K⁆ ≤ ⁅N,K⁆ :=
      hidQ.symm.le.trans (commutator_mono hKN le_rfl)
    _ ≤ ⁅A,K⁆ := hidN.symm.le.trans (commutator_mono hNK le_rfl)
    _ ≤ Z0 := hcentral

include h e hz hk in
/-- The literal plane orbit has nontrivial component movement modulo the
base layer. The normal-generation step preserves the cubic covering kernel. -/
theorem critical_orbit_noncentral
    (hb : sourceDistance h = 2) {c b : Vertex T}
    (hc : CriticalPair T (alpha T) c ((sourceGeometry h).exists_critical _ rfl))
    (hab : Adjacent T (alpha T) b) (hcb : Adjacent T c b) :
    ¬ ⁅criticalOrbit T c b,Ltilde T (alpha T)⁆ ≤ Z T (alpha T) := by
  have hlarge := cubic_core_not_le_frattini h hz hk
  have hgen0 : pResidual 2 M ⊔ T = ⊤ := by
    rw [h.relative_residual]
    apply top_unique
    intro m _
    obtain ⟨k,hkK,t,ht,rfl⟩ := h.relative_product m
    exact mul_mem_sup hkK ht
  let j := embedM T
  let S := (Q T b).comap j
  let Z0 := orbitLayer T
  let E := (Z T c).comap j
  let Y := (criticalPlane T c b).comap j
  let geo := sourceGeometry h
  have hp := h.relative_radical.isPGroup
  have hQR := h.relative_radical.twoCore_le
  have hZr : Z T c ≤ j.range :=
    (critical_Z_le_stabilizer T geo (alpha T) rfl
      (by change 0 < sourceDistance h; omega) hc).trans_eq (stabilizer_m_base _)
  have hEm : E.map j = Z T c := map_comap_eq_self hZr
  have hYmap : Y.map j = criticalPlane T c b :=
    map_comap_eq_self ((criticalPlane_le_opposite c b).trans hZr)
  have hTm : S.map j = Q T b := map_comap_eq_self
    ((show Q T b ≤ stabilizer T (alpha T) from
      fun _ hx => hx.2 _ (adjacent_symm T hab)).trans_eq (stabilizer_m_base _))
  have hc0 := critical_endpoint_color T (alpha T) rfl _ hc
  have hrev := critical_reverse T geo (sourceEdgeCentralizer h e)
    (alpha T) rfl (by change 0 < sourceDistance h; omega) c hc0 hc
  have hE : ¬ E ≤ pCore 2 M := by
    intro he
    apply hrev.2
    rw [←hEm,Q_alpha T hp hQR]
    exact map_mono he
  have hpositive : 0 < criticalDistance T c (geo.exists_critical c hc0) := by
    rw [geo.distance_constant c hc0]
    change 0 < sourceDistance h
    omega
  let := Z_elementary_of_positive T geo c hc0 hpositive
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.comap_of_injective
    (p := 2) j (embedM_injective T) (Z T c)
  have hgen : pResidual 2 M ⊔ S = ⊤ := by
    have hbase : Ltilde T (alpha T) ⊔ Q T (beta T) =
        stabilizer T (alpha T) := by
      rw [Ltilde_alpha,Q_beta,←Subgroup.map_sup,hgen0,
        ←MonoidHom.range_eq_map]
      exact (stabilizer_m_base _).symm
    obtain ⟨g,hg,hgb⟩ := stabilizer_transitive_neighbors T (alpha T)
      (base_adjacent T) hab
    have hh := congrArg (fun H : Subgroup (FreeAmalgam T) =>
      H.map (MulAut.conj g⁻¹).toMonoidHom) hbase
    change act T g (alpha T) = alpha T at hg
    change act T g (beta T) = b at hgb
    rw [Subgroup.map_sup,←Ltilde_act,←Q_act,←stabilizer_act,hg,hgb] at hh
    apply (map_injective (embedM_injective T))
    rw [Subgroup.map_sup,hTm,←Ltilde_alpha,hh,←MonoidHom.range_eq_map]
    exact stabilizer_m_base _
  have hTY : S ≤ normalizer (Y : Set M) := by
    apply le_normalizer_iff.mpr
    intro t ht y hy
    change j (t*y*t⁻¹) ∈ criticalPlane T c b
    rw [map_mul,map_mul,map_inv]
    exact le_normalizer_iff.mp (plane_normalized_edge geo hb hc hab hcb) _ ht _ hy
  have hZQ : Z0 ≤ centralizer (pCore 2 M : Set M) := by
    intro z hz q hq
    apply embedM_injective T
    simp only [map_mul]
    exact (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q T (alpha T) rfl)) hz _
        (Q_alpha T hp hQR ▸ mem_map_of_mem j hq)
  have hQE : ⁅pCore 2 M,E⁆ ≤ E ⊓ pCore 2 M := by
    apply le_inf
    · apply map_le_iff_le_comap.mp
      rw [map_commutator,hEm,←Q_alpha T hp hQR]
      exact DistanceTwo.NaturalCore.local_commutator_le_endpoint hab hcb
    · exact commutator_le_left _ _
  have hne : ¬ ⁅pCore 2 M,pResidual 2 M⁆ ≤ Z0 := by
    intro hh
    have hm := map_mono (f := j) hh
    rw [←core_alpha T hp hQR rfl] at hm
    have hzX := geo.omega_bound (alpha T) rfl
      (by change 0 < sourceDistance h; omega)
    exact hlarge (((hm.trans (map_comap_le _ _)).trans hzX).trans le_sup_right)
  have hd (N : Subgroup M) [N.Normal]
      (hN : N ≤ pCore 2 M) (hfix : N ≤ centralizer (Y : Set M)) :
      ⁅N,E⁆ ≤ Y := by
    apply (map_le_map_iff_of_injective (embedM_injective T)).mp
    rw [map_commutator,hEm,hYmap]
    apply critical_plane_centralizer_displacement h e hz hk hb hc hab hcb
    · rw [Q_alpha T hp hQR]
      exact map_mono hN
    · rw [←hYmap]
      rintro _ ⟨n,hnN,rfl⟩ _ ⟨y,hy,rfl⟩
      exact (map_mul j y n).symm.trans
        ((congrArg j (hfix hnN y hy)).trans (map_mul j n y))
  have hnc := normal_orbit_noncentral h e hz S Z0 E Y (IsElementaryAbelian.isPGroup 2 E)
    (h.relative_residual ▸ hgen) hTY (comap_mono (criticalPlane_le_opposite c b)) hZQ hE hQE (h.relative_residual ▸ hne) hd
  intro hh
  apply hnc
  rw [←h.relative_residual]
  apply map_le_iff_le_comap.mp
  rw [map_commutator,←Ltilde_alpha]
  exact hh


include h e hz hk in
/-- The generating plane escapes the canonical fixed preimage before any
local plane equality or favorable-pair estimate is supplied. -/
theorem critical_plane_not_fixed
    (hb : sourceDistance h = 2)
    {c b : Vertex T}
    (hc : CriticalPair T (alpha T) c
      ((sourceGeometry h).exists_critical _ rfl))
    (hab : Adjacent T (alpha T) b) (hcb : Adjacent T c b) :
    ¬ (criticalPlane T c b).comap (embedM T) ≤
      orbitFixedKernel (pResidual 2 M) T c b := by
  apply plane_not_fixed_of_movement
  intro hm
  have hh := map_mono (f := embedM T) hm
  rw [map_commutator,←Ltilde_alpha] at hh
  exact critical_orbit_noncentral h e hz hk hb hc hab hcb
    (hh.trans (map_comap_le _ _))

end AlternatingSixReconstruction.Exceptional.Exhaustion.CubicAction
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
