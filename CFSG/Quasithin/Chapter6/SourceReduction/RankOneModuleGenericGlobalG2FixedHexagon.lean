module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2WeylLocalization
public import Theory.GroupAction.DihedralPolygon.FixedHexagon
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2WeylTorus
import all Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.InnerFieldCoverage.FrameAlignment.RankOneNormalizers

/-!
# Closing the canonical G₂ Weyl rotation in a small completion

Hall conjugacy inside the actual Borel adjusts a torus-fixed neighbor into
its torus normalizer. The checked rank-one normalizer covers then leave
exactly the two Weyl neighbors at each endpoint, also over F₄. These
calculations transfer through both embeddings and their whole overlap.

The established girth bound fixes every short geodesic between torus-fixed
vertices. If the completion has diameter at most six, the thin fixed-graph
argument closes the canonical twelve-arc. Its sixth rotation power lies in
the original Borel, and the proved torus-centralizer and cube-inversion
identities kill it. An actual twelve-cycle also suffices, by the existing
seven-path-transitivity argument. Concrete recognition follows with no
additional Weyl relation.

The source application uses the literal original coset graph. Its diameter
bound remains an ambient obligation; neither exhaustive amalgam selection
nor original uniqueness is asserted here. The internal imports retain the
existing torus-coordinate and rank-one-normalizer boundaries. Their native
calculations retain LICENSES/ATLAS.txt attribution.
Source: Aschbacher–Smith F.3.6, F.4.8 and F.4.24–26, printed pp.272,278,
287–288, and 5.3.3–4, p.659 (`refs/quasithin.pdf`).
-/

open Subgroup Theory.GroupTheory Atlas.G2 Atlas.G2.LieParabolicSetup
open Atlas.G2.LieAutomorphismExtensions.InnerFieldCoverage
open Subgroup.CosetGeometry Subgroup.CosetGeometry.RankTwo
public noncomputable section
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.G2CompletionGeometry

private theorem hall_adjust {X : Type*} [Group X] [Finite X]
    (D B : Subgroup X) (hDB : D ≤ B) (hsolv : Group.IsSolvable B)
    (hHall : IsHallSubgroup Subgroup.OddHall.oddPrimes (D.subgroupOf B))
    (g : X) (hg : D.map (MulAut.conj g⁻¹).toMonoidHom ≤ B) :
    ∃ b ∈ B, g*b ∈ normalizer (D : Set X) := by
  let E := D.map (MulAut.conj g⁻¹).toMonoidHom
  have hcard : Nat.card (E.subgroupOf B) = Nat.card (D.subgroupOf B) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hg).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hDB).toEquiv]
    exact card_map_of_injective (MulAut.conj g⁻¹).injective
  have hidx : (E.subgroupOf B).index = (D.subgroupOf B).index := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := D.subgroupOf B))
    rw [←hcard,(E.subgroupOf B).card_mul_index,hcard,(D.subgroupOf B).card_mul_index]
  have hE : IsHallSubgroup Subgroup.OddHall.oddPrimes (E.subgroupOf B) := by
    refine ⟨?_,?_⟩
    · intro p hp
      exact hHall.p_in_pi_of_p_dvd_card p (hcard ▸ hp)
    · intro p hp
      exact hHall.p_in_pi_of_p_dvd_index p (hidx ▸ hp)
  obtain ⟨b,hb⟩ := exists_conj_eq_of_isHallSubgroup_of_solvable hsolv hHall hE
  have he : D.map (MulAut.conj b.val).toMonoidHom = E := by
    have hh := congrArg (Subgroup.map B.subtype) hb
    rw [map_map] at hh
    have hc : B.subtype.comp (MulAut.conj b).toMonoidHom =
        (MulAut.conj b.val).toMonoidHom.comp B.subtype := rfl
    rw [hc,←map_map,map_subgroupOf_eq_of_le hDB,map_subgroupOf_eq_of_le hg] at hh
    exact hh.symm
  refine ⟨b,b.property,mem_normalizer_iff_map_conj_eq.mpr ?_⟩
  have hc : (MulAut.conj (g*b.val)).toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp (MulAut.conj b.val).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply,mul_assoc]
  change D.map (MulAut.conj (g*b.val)).toMonoidHom = D
  rw [hc,←map_map,he]
  change (D.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = D
  rw [map_map]
  have hi : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom = MonoidHom.id X := by
    ext x
    simp [MulAut.conj_apply,mul_assoc]
  rw [hi,map_id]

variable {F : Type} [Field F] [Finite F] [CharP F 2]
private theorem native_fixed_coset
    (P : Subgroup (Model F)) (hBP : Atlas.G2.borel ≤ P) (w : Model F)
    (hcover : RankOneTorusNormalizerCover P w)
    (hw : w ∈ normalizer (splitTorus (K := F) : Set (Model F)))
    (g : Model F) (hg : g∈P)
    (hfix : ∀ t ∈ splitTorus, g⁻¹*t*g ∈ Atlas.G2.borel) :
    g∈Atlas.G2.borel ∨ ∃ b∈Atlas.G2.borel,g=w*b := by
  have hh : IsHallSubgroup Subgroup.OddHall.oddPrimes (EvenBorelTorus.complement (F := F)) :=
    Subgroup.OddHall.oddHall_of_normalized_sup unipotent_isTwoGroup
      (Nat.coprime_two_left.mpr EvenBorelTorus.card_torus_odd)
      EvenBorelTorus.torus_le_normalizer rfl
  obtain ⟨b,hb,hn⟩ := hall_adjust splitTorus Atlas.G2.borel le_sup_right
    DerivedNormalizerSolvable.isSolvable_borel hh g (by
      rintro x ⟨t,ht,rfl⟩
      simpa only [MulEquiv.coe_toMonoidHom,MulAut.conj_apply,inv_inv] using hfix t ht)
  rcases hcover (g*b) (P.mul_mem hg (hBP hb)) hn with hd | ⟨l,m,he⟩
  · left
    have hm := Atlas.G2.borel.mul_mem (mem_sup_right hd) (Atlas.G2.borel.inv_mem hb)
    simpa only [mul_inv_cancel_right] using hm
  · right
    have ht : w⁻¹*torus l m*w ∈ splitTorus := by
      simpa only [inv_inv] using (mem_normalizer_iff.mp ((normalizer _).inv_mem hw)
        (torus l m)).mp (show torus l m ∈ splitTorus from ⟨(l,m),rfl⟩)
    refine ⟨(w⁻¹*torus l m*w)*b⁻¹,Atlas.G2.borel.mul_mem (mem_sup_right ht) (Atlas.G2.borel.inv_mem hb),?_⟩
    have hh : g=(torus l m*w)*b⁻¹ := (eq_mul_inv_iff_mul_eq.mpr he)
    rw [hh]
    group

namespace Completion
variable {G : Type*} [Group G] (c : Completion F G)
local notation "x" => RankTwo.base c.cosetFamily false
local notation "y" => RankTwo.base c.cosetFamily true
local notation "s" => c.left nativeS
local notation "r" => c.right nativeR

def TorusFixed (v : c.Vertex) : Prop := ∀ p, c.torusMap p • v=v

omit [Finite F] [CharP F 2] in
private theorem fixes_base_iff (g : G) (i : Bool) :
    g • RankTwo.base c.cosetFamily i=RankTwo.base c.cosetFamily i ↔
      g∈c.cosetFamily i := by
  change g∈stabilizer c.cosetFamily (RankTwo.base c.cosetFamily i) ↔ _
  simp only [stabilizer,RankTwo.base,stabilizer_base]

omit [Finite F] [CharP F 2] in
private theorem left_mem_middle_iff (u : parabolic₁ (F := F)) :
    c.left u∈c.middle.range ↔ u.val∈Atlas.G2.borel := by
  constructor
  · rintro ⟨b,hb⟩
    have he := c.left_injective hb
    exact parabolics_intersection.le (congrArg Subtype.val he ▸ b.property)
  · intro hu
    exact ⟨⟨u.val,parabolics_intersection.ge hu⟩,rfl⟩

omit [Finite F] [CharP F 2] in
private theorem right_mem_middle_iff (u : parabolic₂ (F := F)) :
    c.right u∈c.middle.range ↔ u.val∈Atlas.G2.borel := by
  constructor
  · rintro ⟨b,hb⟩
    have he := c.right_injective ((DFunLike.congr_fun c.compatible b).symm.trans hb)
    exact parabolics_intersection.le (congrArg Subtype.val he ▸ b.property)
  · intro hu
    exact ⟨⟨u.val,parabolics_intersection.ge hu⟩,
      DFunLike.congr_fun c.compatible ⟨u.val,parabolics_intersection.ge hu⟩⟩

omit [Finite F] [CharP F 2] in
private theorem torus_fixed_base (i : Bool) : c.TorusFixed (RankTwo.base c.cosetFamily i) := by
  intro p
  apply (c.fixes_base_iff _ _).mpr
  cases i
  · exact c.middle_le_left (c.markedTorus_le_middle ⟨p,rfl⟩)
  · exact c.middle_le_right (c.markedTorus_le_middle ⟨p,rfl⟩)

omit [Finite F] [CharP F 2] in
private theorem torus_fixed_involution (u : G) (hu : u^2=1)
    (hrot : ∀p,∃q,MulAut.conj u (c.torusMap p)=c.torusMap q) (v : c.Vertex) :
    c.TorusFixed (u • v) ↔ c.TorusFixed v := by
  have huu : u*u=1 := by simpa only [pow_two] using hu
  have hui : u⁻¹=u := inv_eq_of_mul_eq_one_right huu
  have hf (z : c.Vertex) (hz : c.TorusFixed z) : c.TorusFixed (u • z) := by
    intro p
    obtain ⟨q,hq⟩ := hrot p
    have he : u*c.torusMap p*u=c.torusMap q := by
      simpa only [MulAut.conj_apply,hui] using hq
    calc
      c.torusMap p • (u • z) = u • ((u*c.torusMap p*u) • z) := by
        simp only [mul_smul,←mul_smul u u,huu,one_smul]
      _ = u • z := by rw [he,hz q]
  refine ⟨fun hv => ?_,hf v⟩
  simpa only [←mul_smul,huu,one_smul] using hf (u • v) hv

omit [Finite F] [CharP F 2] in
private theorem torus_fixed_S (v : c.Vertex) : c.TorusFixed (s • v) ↔ c.TorusFixed v :=
  c.torus_fixed_involution s (by rw [←map_pow,show nativeS^2=(1:parabolic₁ (F:=F)) from Subtype.ext weylS_sq,map_one])
    (fun p => ⟨(p.2,p.1),c.weylS_torusMap _ _⟩) v

omit [Finite F] [CharP F 2] in
private theorem torus_fixed_R (v : c.Vertex) : c.TorusFixed (r • v) ↔ c.TorusFixed v :=
  c.torus_fixed_involution r (by rw [←map_pow,show nativeR^2=(1:parabolic₂ (F:=F)) from Subtype.ext weylR_sq,map_one])
    (fun p => ⟨(p.1,p.1*p.2⁻¹),c.weylR_torusMap _ _⟩) v

omit [Finite F] [CharP F 2] in
private theorem left_conjugate_fixed (hc : c.left.range ⊓ c.right.range=c.middle.range)
    (u a : parabolic₁ (F := F))
    (hh : c.left a • (c.left u • y)=c.left u • y) : (u⁻¹*a*u).val∈Atlas.G2.borel := by
  have he : c.left (u⁻¹*a*u) • y=y := by
    simpa only [map_mul,map_inv,mul_smul,inv_smul_smul] using
      congrArg ((c.left u)⁻¹ • ·) hh
  apply (c.left_mem_middle_iff _).mp
  exact hc ▸ show c.left (u⁻¹*a*u)∈c.left.range⊓c.right.range from
    ⟨⟨_,rfl⟩,(c.fixes_base_iff _ true).mp he⟩

omit [Finite F] [CharP F 2] in
private theorem right_conjugate_fixed (hc : c.left.range ⊓ c.right.range=c.middle.range)
    (u a : parabolic₂ (F := F))
    (hh : c.right a • (c.right u • x)=c.right u • x) : (u⁻¹*a*u).val∈Atlas.G2.borel := by
  have he : c.right (u⁻¹*a*u) • x=x := by
    simpa only [map_mul,map_inv,mul_smul,inv_smul_smul] using
      congrArg ((c.right u)⁻¹ • ·) hh
  apply (c.right_mem_middle_iff _).mp
  exact hc ▸ show c.right (u⁻¹*a*u)∈c.left.range⊓c.right.range from
    ⟨(c.fixes_base_iff _ false).mp he,⟨_,rfl⟩⟩

/-- The whole marked torus fixes only the two standard neighbors on the short side. -/
theorem torus_fixed_neighbors_left (hq : 2 < Nat.card F)
    (hc : c.left.range ⊓ c.right.range=c.middle.range)
    (v : c.Vertex) (hv : c.graph.Adj x v) (hQ : c.TorusFixed v) :
    v=y ∨ v=s • y := by
  obtain ⟨g,⟨u,rfl⟩,he⟩ := neighbor_base_rep c.cosetFamily false hv
  have he' : c.left u • y=v := by
    change c.left u • mkVertex c.cosetFamily true 1=v
    simpa only [smul_mkVertex,mul_one,Bool.not_false,Bool.not_true] using he
  have ht : ∀ t∈splitTorus,u.val⁻¹*t*u.val∈Atlas.G2.borel := by
    rintro t ⟨p,rfl⟩
    exact c.left_conjugate_fixed hc u (nativeTorus₁ p) (by
      change c.torusMap p • (c.left u • y)=c.left u • y
      rw [he']; exact hQ p)
  rcases native_fixed_coset parabolic₁ borel_le_parabolic₁ weylS
    (rankOne_torusNormalizerCover_short hq) weylS_mem_torusNormalizer u.val u.property ht with hu | ⟨b,hb,hub⟩
  · left
    exact he'.symm.trans ((c.fixes_base_iff _ true).mpr
      (c.middle_le_right ((c.left_mem_middle_iff _).mpr hu)))
  · right
    let b' : parabolic₁ (F := F) := ⟨b,borel_le_parabolic₁ hb⟩
    have hu' : u=nativeS*b' := Subtype.ext hub
    have hb' : c.left b' • y=y := (c.fixes_base_iff _ true).mpr
      (c.middle_le_right ((c.left_mem_middle_iff _).mpr hb))
    rw [←he',hu',map_mul,mul_smul,hb']

/-- The long endpoint has the same two-neighbor fixed graph, through its own map. -/
theorem torus_fixed_neighbors_right (hq : 2 < Nat.card F)
    (hc : c.left.range ⊓ c.right.range=c.middle.range)
    (v : c.Vertex) (hv : c.graph.Adj y v) (hQ : c.TorusFixed v) :
    v=x ∨ v=r • x := by
  obtain ⟨g,⟨u,rfl⟩,he⟩ := neighbor_base_rep c.cosetFamily true hv
  have he' : c.right u • x=v := by
    change c.right u • mkVertex c.cosetFamily false 1=v
    simpa only [smul_mkVertex,mul_one,Bool.not_false,Bool.not_true] using he
  have ht : ∀ t∈splitTorus,u.val⁻¹*t*u.val∈Atlas.G2.borel := by
    rintro t ⟨p,rfl⟩
    exact c.right_conjugate_fixed hc u (nativeTorus₂ p) (by
      rw [←c.torusMap_right]
      rw [he']; exact hQ p)
  rcases native_fixed_coset parabolic₂ borel_le_parabolic₂ weylR
    (rankOne_torusNormalizerCover_long hq) weylR_mem_torusNormalizer u.val u.property ht with hu | ⟨b,hb,hub⟩
  · left
    exact he'.symm.trans ((c.fixes_base_iff _ false).mpr
      (c.middle_le_left ((c.right_mem_middle_iff _).mpr hu)))
  · right
    let b' : parabolic₂ (F := F) := ⟨b,borel_le_parabolic₂ hb⟩
    have hu' : u=nativeR*b' := Subtype.ext hub
    have hb' : c.right b' • x=x := (c.fixes_base_iff _ false).mpr
      (c.middle_le_left ((c.right_mem_middle_iff _).mpr hb))
    rw [←he',hu',map_mul,mul_smul,hb']

/-- Thin torus-fixed neighborhoods and the existing girth bound force the
canonical Weyl relation in any completion of diameter at most six. -/
theorem weylProduct_six_eq_one_of_diameter (hq : 2 < Nat.card F)
    (hc : c.left.range ⊓ c.right.range=c.middle.range)
    (hdiam : ∀v w,c.graph.dist v w≤6) : c.weylProduct^6=1 := by
  have hs : s^2=1 := by
    rw [←map_pow,show nativeS^2=(1:parabolic₁ (F:=F)) from Subtype.ext weylS_sq,map_one]
  have hr : r^2=1 := by
    rw [←map_pow,show nativeR^2=(1:parabolic₂ (F:=F)) from Subtype.ext weylR_sq,map_one]
  have hsx : s • x=x := (c.fixes_base_iff _ false).mpr ⟨_,rfl⟩
  have hry : r • y=y := (c.fixes_base_iff _ true).mpr ⟨_,rfl⟩
  have hsy : s • y≠y := by
    intro hh
    have hm : s∈c.middle.range := hc ▸
      show s∈c.left.range⊓c.right.range from ⟨⟨_,rfl⟩,(c.fixes_base_iff _ true).mp hh⟩
    exact Native.first_not_mem F false
      (borel_le_parabolic₂ ((c.left_mem_middle_iff _).mp hm))
  have hrx : r • x≠x := by
    intro hh
    have hm : r∈c.middle.range := hc ▸
      show r∈c.left.range⊓c.right.range from ⟨(c.fixes_base_iff _ false).mp hh,⟨_,rfl⟩⟩
    exact Native.first_not_mem F true
      (borel_le_parabolic₁ ((c.right_mem_middle_iff _).mp hm))
  have hh := GroupAction.DihedralPolygon.fixed_edge_sequence_closes c.bipartiteAction
    s r x y hs hr hsx hry ⟨Bool.false_ne_true,incident_base c.cosetFamily false true⟩
    hsy hrx c.connected hdiam (c.cycle_length_ge_twelve hc)
    c.TorusFixed (c.torus_fixed_base false) (c.torus_fixed_base true)
    c.torus_fixed_S c.torus_fixed_R (c.torus_fixed_neighbors_left hq hc)
    (c.torus_fixed_neighbors_right hq hc) (by
      intro v w p hp hl hv hw u hu z
      exact SimpleGraph.short_geodesic_fixed (c.cycle_length_ge_twelve hc) c.graphAction
        p hp hl _ (hv z) (hw z) u hu)
  have hm : c.weylProduct^6∈c.left.range :=
    (c.fixes_base_iff _ false).mp
      (GroupAction.DihedralPolygon.inverse_rotation_fixed hr hs hh.1)
  exact c.weylProduct_six_eq_one_of_mem
    ((c.left_torus_centralizer hq).le ⟨hm,c.weylProduct_six_mem_centralizer⟩)

/-- An actual twelve-cycle suffices; seven-path transitivity supplies the
diameter bound and the torus argument supplies the canonical Weyl relation. -/
theorem nonempty_mulEquiv_of_twelve_cycle (hq : 2 < Nat.card F)
    (hc : c.left.range ⊓ c.right.range=c.middle.range)
    (hex : ∃v,∃p : c.graph.Walk v v,p.IsCycle ∧ p.length=12) :
    Nonempty (G ≃* Model F) := by
  apply c.nonempty_mulEquiv_of_weyl hc
  apply c.weylProduct_six_eq_one_of_diameter hq hc
  apply SimpleGraph.PathTransitivePolygon.HexagonRecognition.diameter_bound_of_seven_endpoint_bound c.connected
  intro v p hp
  exact SimpleGraph.PathTransitivePolygon.HexagonRecognition.seven_endpoint_bound
    c.graphAction (c.seven_transitive hc) (·.type) (fun h => h.1)
    (fun h => (same_orbit_iff c.cosetFamily _ _).mpr h) hex p hp

end Completion

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.G2CompletionGeometry

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open G2CompletionGeometry
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}

/-- A diameter bound on the literal original coset graph discharges the
canonical Weyl relation and yields the concrete model at the original degree.
The diameter bound remains an ambient source obligation. -/
theorem Preparation.g2_ambient_recognition_of_diameter
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)
    (hdiam : let P : Bool → Subgroup G := fun i =>
        ChapterF.Source.parabolic ![L,residual H] (sourceS L H) (if i then 0 else 1)
      ∀ v w : RankTwo.Vertex P, (RankTwo.graph P).dist v w ≤ 6) :
    Nat.card F=2^n ∧ Nonempty (G ≃* Model F) := by
  obtain ⟨c,hl,hr,_,ho,_,_,_⟩ := d.g2_ambient_completion_geometry h hH hp F e
  have hF := (d.g2_local_structure h hH.1.1.2 hp F (Or.inr ⟨e⟩)).1
  have hq : 2 < Nat.card F := by
    rw [hF]
    exact Nat.pow_lt_pow_right (by decide : 1 < (2:ℕ)) h.exponent
  have hfamily : c.cosetFamily = fun i =>
      ChapterF.Source.parabolic ![L,residual H] (sourceS L H) (if i then 0 else 1) := by
    funext i
    have her : e.right.symm.toMonoidHom.range=⊤ := MonoidHom.range_eq_top.mpr e.right.symm.surjective
    have hel : e.left.symm.toMonoidHom.range=⊤ := MonoidHom.range_eq_top.mpr e.left.symm.surjective
    cases i
    · change c.left.range=_
      rw [hl,MonoidHom.range_comp,her,←MonoidHom.range_eq_map,range_subtype]
      simp only [Bool.false_eq_true,↓reduceIte]
    · change c.right.range=_
      rw [hr,MonoidHom.range_comp,hel,←MonoidHom.range_eq_map,range_subtype]
      simp only [↓reduceIte]
  refine ⟨hF,c.nonempty_mulEquiv_of_weyl ho (c.weylProduct_six_eq_one_of_diameter hq ho ?_)⟩
  change ∀ v w : RankTwo.Vertex c.cosetFamily, (RankTwo.graph c.cosetFamily).dist v w≤6
  rw [hfamily]
  exact hdiam

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
