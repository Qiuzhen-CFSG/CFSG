module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Center.Frattini

/-!
# The three literal Frattini sections in the distance-eight core

The first dual quotient restricts to Phi(Q)/Z(Q). The second doubled-dual
quotient restricts to the intersection of the second hat with Q, which the
Frattini calculation identifies with C_Q(Phi(Q)). The commutator-row natural
pair restricts to Q/C_Q(Phi(Q)). Surjectivity uses the actual central
supplement; every section retains the same CommonFacts marking and action.

The only extra premise is the whole fixed-factor equality owned by
qt-ms93-distance-eight-fixed-factor. The original-input applications in
BinaryCenter/DistanceEightFrattini and DistanceEightFrattiniPairs transport all
three sections. The final C.1.34 assembly remains with qt-rank-two-ms93.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5)(v)--(vii), printed p.895;
Aschbacher--Smith C.1.34(4), printed p.136.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Center
open Higher NormalizerTransfer
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {geometry : Geometry R} {source : LocalSource L R}

private theorem restricted_onto {G B : Type*} [Group G] [Group B]
    {A N D : Subgroup G} (f : A →* B) (hf : Function.Surjective f)
    (hk : f.ker = N.subgroupOf A) (hDA : D ≤ A) (hNA : N ≤ A)
    (hn : D ≤ normalizer N) (hs : D ⊔ N = A) :
    Function.Surjective (f.comp (inclusion hDA)) := by
  intro v
  obtain ⟨x,rfl⟩ := hf v
  have hx : (x : G) ∈ (D : Set G) * (N : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right _ _ hn,hs]
    exact x.property
  obtain ⟨d,hd,n,hn',he⟩ := hx
  refine ⟨⟨d,hd⟩,?_⟩
  have hx' : x = inclusion hDA ⟨d,hd⟩ * inclusion hNA ⟨n,hn'⟩ := Subtype.ext he.symm
  have hn0 : f (inclusion hNA ⟨n,hn'⟩) = 1 := MonoidHom.mem_ker.mp (hk ▸ hn')
  change f (inclusion hDA ⟨d,hd⟩) = f x
  rw [hx',map_mul,hn0,mul_one]

omit [Finite M] in
private theorem restrict_dual (common : CommonFacts R source geometry)
    {A N D : Subgroup (FreeAmalgam R)} (s : MarkedDualSection source common A N)
    (hDA : D ≤ A) (hD : Mbar R ≤ normalizer D)
    (hn : D ≤ normalizer N) (hs : D ⊔ N = A) :
    Nonempty (MarkedDualSection source common D (D ⊓ N)) := by
  refine ⟨{ local_group := hDA.trans s.local_group
            lower_le := inf_le_left
            normalized := hD
            quotient := s.quotient.comp (inclusion hDA)
            onto := restricted_onto s.quotient s.onto s.kernel hDA s.lower_le hn hs
            kernel := ?_
            action := ?_ }⟩
  · ext x
    change inclusion hDA x ∈ s.quotient.ker ↔ _
    rw [s.kernel]
    exact ⟨fun hx => ⟨x.property,hx⟩,fun hx => hx.2⟩
  · intro m x y hy
    exact s.action m (inclusion hDA x) (inclusion hDA y) hy

omit [Finite M] in
private theorem restrict_pair (common : CommonFacts R source geometry)
    {A N D : Subgroup (FreeAmalgam R)} {b : Bool}
    (s : MarkedPairSection source common A N b)
    (hDA : D ≤ A) (hD : Mbar R ≤ normalizer D)
    (hn : D ≤ normalizer N) (hs : D ⊔ N = A) :
    Nonempty (MarkedPairSection source common D (D ⊓ N) b) := by
  refine ⟨{ local_group := hDA.trans s.local_group
            lower_le := inf_le_left
            normalized := hD
            quotient := s.quotient.comp (inclusion hDA)
            onto := restricted_onto s.quotient s.onto s.kernel hDA s.lower_le hn hs
            kernel := ?_
            action := ?_ }⟩
  · ext x
    change inclusion hDA x ∈ s.quotient.ker ↔ _
    rw [s.kernel]
    exact ⟨fun hx => ⟨x.property,hx⟩,fun hx => hx.2⟩
  · intro m x y hy
    exact s.action m (inclusion hDA x) (inclusion hDA y) hy

/-- The single dual section on the literal Frattini subgroup modulo the entire
core center. Its coordinates use the original common marking. -/
theorem frattini_marked_dual_of_fixedFactor
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    (hfixed : core R (alpha R) ⊓ centralizer
      (Ltilde R (alpha R) : Set (FreeAmalgam R)) = H R (alpha R)) :
    Nonempty (MarkedDualSection source common
      ((frattini (core R (alpha R))).map (core R (alpha R)).subtype)
      ((center (core R (alpha R))).map (core R (alpha R)).subtype)) := by
  obtain ⟨p⟩ := Early.sourcePath_nonempty source common earlier (alpha R) rfl
  obtain ⟨s⟩ := Quotients.FirstDirect.markedDualSection common earlier p
  rw [core_frattini_eq_moving_of_fixedFactor common earlier hfixed,
    core_center_eq_U_sup_fixedFactor common earlier,hfixed,
    ← moving_inf_Z_eq_U_sup_H common earlier p]
  apply restrict_dual common s
  · rw [(Early.Orbit.Source.Complete.sourceOrbitFacts common earlier p).hatV_eq]
    exact le_sup_left
  · simpa only [alpha,stabilizer_m_base] using Vcirc_normalized (R := R) (alpha R)
  · exact ((Vcirc_le_V R _).trans (geometry.V_local _ rfl common.large_distance)).trans
      (Z_normalized R _)
  · exact (Early.Orbit.Source.Complete.sourceOrbitFacts common earlier p).hatV_eq.symm

private theorem second_eq_intersection_sup_Z (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R)) :
    (core R (alpha R) ⊓ hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)) ⊔
        Z R (alpha R) = hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) := by
  let K := core R (alpha R)
  let B := hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)
  let Z₀ := Z R (alpha R)
  obtain ⟨s⟩ := Quotients.SecondLayer.OrbitSource.marked_pair common earlier p
  have hZA : Z₀ ≤ hatV R (alpha R) (p.walk.getVert 6) := by
    rw [(Early.Orbit.Source.Complete.sourceOrbitFacts common earlier p).hatV_eq]
    exact le_sup_right
  have hZB : Z₀ ≤ B := hZA.trans s.lower_le
  have hn : K ≤ normalizer Z₀ := ((DistanceTwo.core_le_Q _).trans (fun _ hx => hx.1)).trans
    (Z_normalized R _)
  apply le_antisymm (sup_le inf_le_right hZB)
  intro b hb
  have hb' : b ∈ (K : Set (FreeAmalgam R)) * (Z₀ : Set (FreeAmalgam R)) := by
    rw [← coe_mul_of_left_le_normalizer_right _ _ hn]
    exact second_le_core_sup_Z common earlier p hb
  obtain ⟨k,hk,z,hz,rfl⟩ := hb'
  have hkB : k ∈ B := by
    have hh := B.mul_mem hb (B.inv_mem (hZB hz))
    simpa only [mul_inv_cancel_right] using hh
  exact mul_mem (mem_sup_left ⟨hk,hkB⟩) (mem_sup_right hz)

/-- The two dual copies on the centralizer of the actual Frattini subgroup. -/
theorem frattini_centralizer_marked_pair_of_fixedFactor
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    (hfixed : core R (alpha R) ⊓ centralizer
      (Ltilde R (alpha R) : Set (FreeAmalgam R)) = H R (alpha R)) :
    let Phi := (frattini (core R (alpha R))).map (core R (alpha R)).subtype
    Nonempty (MarkedPairSection source common
      (core R (alpha R) ⊓ centralizer (Phi : Set (FreeAmalgam R))) Phi true) := by
  dsimp only
  obtain ⟨p⟩ := Early.sourcePath_nonempty source common earlier (alpha R) rfl
  obtain ⟨s⟩ := Quotients.SecondLayer.OrbitSource.marked_pair common earlier p
  rw [core_frattini_centralizer_of_fixedFactor common earlier hfixed p,
    core_frattini_eq_moving_of_fixedFactor common earlier hfixed]
  have hkernel : (core R (alpha R) ⊓
      hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)) ⊓
      hatV R (alpha R) (p.walk.getVert 6) = Vcirc R (alpha R) := by
    rw [inf_assoc,inf_eq_right.mpr s.lower_le]
    exact core_inf_first_eq_moving_of_fixedFactor common earlier hfixed p
  rw [← hkernel]
  apply restrict_pair common s inf_le_right
  · have hn : Mbar R ≤ normalizer (core R (alpha R)) := HomSaturation.core_normalized
    exact le_normalizer_inf hn s.normalized
  · exact (inf_le_right.trans s.local_group).trans (hatV_normalized R _ _)
  · apply le_antisymm (sup_le inf_le_right s.lower_le)
    apply (second_eq_intersection_sup_Z common earlier p).ge.trans
    apply sup_le le_sup_left
    apply le_trans _ le_sup_right
    rw [(Early.Orbit.Source.Complete.sourceOrbitFacts common earlier p).hatV_eq]
    exact le_sup_right

/-- The two natural copies on the original core modulo its Frattini centralizer. -/
theorem core_frattini_centralizer_marked_pair_of_fixedFactor
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    (hfixed : core R (alpha R) ⊓ centralizer
      (Ltilde R (alpha R) : Set (FreeAmalgam R)) = H R (alpha R)) :
    let Phi := (frattini (core R (alpha R))).map (core R (alpha R)).subtype
    Nonempty (MarkedPairSection source common (core R (alpha R))
      (core R (alpha R) ⊓ centralizer (Phi : Set (FreeAmalgam R))) false) := by
  dsimp only
  obtain ⟨p⟩ := Early.sourcePath_nonempty source common earlier (alpha R) rfl
  obtain ⟨s⟩ := core_second_marked_natural_pair common earlier p
  rw [core_frattini_centralizer_of_fixedFactor common earlier hfixed p]
  apply restrict_pair common s le_sup_left HomSaturation.core_normalized
  · exact ((DistanceTwo.core_le_Q _).trans (fun _ hx => hx.1)).trans
      (hatW_normalized R _ _ _)
  · rfl

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Center
