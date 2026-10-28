module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoCoreSpan
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.PathControl

/-!
# The paired D calculation in the noncentral b=2 branch

Opposite fixed spaces in the center section and the two Sylow-product
covers split the literal D as R Z, where R is its intersection with the
two critical endpoint cores. These covers concern D, not the whole core.
The critical centers normalize D, so D is normal in the actual local
actor. Its Frattini image equals that of R. The two residuals lie in the
opposite D, making their Frattini images equal; the faithful local-cover
argument kills this common subgroup. Finally, elementary abelianness
makes R central in the actor, so R lies in its Sylow omega-center and
D equals Z.

The paired geometry is an explicit intermediate contract. Its constructor
must supply the covers and fixed-space span from the marked Chapter 7
actions. This proves the subgroup and Frattini steps in 10.4/10.6, not
unconditional 10.6 or the remaining 10.9/10.10 alternatives.
Source: DGS, *Groups and Graphs* (1985), notation p.153, 10.4 pp.155--156,
and the proof of 10.6 p.157.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting
variable {G : Type*} [Group G]

private theorem central_supplement_intersection (A D Z B : Subgroup G)
    (hc : Z ≤ centralizer (D : Set G)) (hA : A = Z ⊔ D) (hDB : D ≤ B) :
    A ⊓ B = (Z ⊓ B) ⊔ D := by
  apply le_antisymm
  · rintro x ⟨hxA,hxB⟩
    have hx : x ∈ (Z : Set G) * (D : Set G) := by
      rw [← coe_mul_of_left_le_normalizer_right Z D
        (hc.trans (Subgroup.centralizer_le_normalizer _)), ← hA]
      exact hxA
    obtain ⟨z,hz,d,hd,rfl⟩ := hx
    have hzB : z ∈ B := by
      simpa only [mul_inv_cancel_right] using B.mul_mem hxB (B.inv_mem (hDB hd))
    exact ((Z ⊓ B) ⊔ D).mul_mem
      ((le_sup_left : Z ⊓ B ≤ (Z ⊓ B) ⊔ D) ⟨hz,hzB⟩)
      ((le_sup_right : D ≤ (Z ⊓ B) ⊔ D) hd)
  · exact sup_le (le_inf (inf_le_left.trans ((le_sup_left : Z ≤ Z ⊔ D).trans hA.ge)) inf_le_right)
      (le_inf ((le_sup_right : D ≤ Z ⊔ D).trans hA.ge) hDB)

private theorem two_central_supplements (A Z B C : Subgroup G)
    (hZA : Z ≤ A) (hc : Z ≤ centralizer (A : Set G))
    (hAB : A ≤ Z ⊔ B) (hAC : A ≤ Z ⊔ C)
    (hnB : Z ≤ normalizer (B : Set G)) (hnC : Z ≤ normalizer (C : Set G))
    (hZ : Z = (Z ⊓ B) ⊔ (Z ⊓ C)) (hBC : B ⊓ C ≤ A) :
    A = Z ⊔ (B ⊓ C) := by
  have hfactor (R : Subgroup G) (hn : Z ≤ normalizer (R : Set G))
      (hAR : A ≤ Z ⊔ R) : A = Z ⊔ (A ⊓ R) := by
    apply le_antisymm
    · intro a ha
      have hx : a ∈ (Z : Set G) * (R : Set G) := by
        rw [← coe_mul_of_left_le_normalizer_right Z R hn]
        exact hAR ha
      obtain ⟨z,hz,r,hr,rfl⟩ := hx
      have hrA : r ∈ A := by
        simpa only [inv_mul_cancel_left] using A.mul_mem (A.inv_mem (hZA hz)) ha
      exact (Z ⊔ (A ⊓ R)).mul_mem
        ((le_sup_left : Z ≤ Z ⊔ (A ⊓ R)) hz)
        ((le_sup_right : A ⊓ R ≤ Z ⊔ (A ⊓ R)) ⟨hrA,hr⟩)
    · exact sup_le hZA inf_le_left
  have hB := hfactor B hnB hAB
  have hC := hfactor C hnC hAC
  have hBA : A = (Z ⊓ C) ⊔ (A ⊓ B) := by
    calc
      A = Z ⊔ (A ⊓ B) := hB
      _ = ((Z ⊓ B) ⊔ (Z ⊓ C)) ⊔ (A ⊓ B) := congrArg (· ⊔ (A ⊓ B)) hZ
      _ = _ := by
        rw [sup_comm (Z ⊓ B), sup_assoc]
        congr 1
        exact sup_eq_right.mpr (le_inf (inf_le_left.trans hZA) inf_le_right)
  have hCI := central_supplement_intersection A (Z ⊓ C) (A ⊓ B) C
    (inf_le_left.trans ((le_centralizer_iff.mp hc).trans (centralizer_le inf_le_left)))
    (hBA.trans (sup_comm _ _)) inf_le_right
  have hABC : (A ⊓ B) ⊓ C = B ⊓ C := by
    rw [inf_assoc, inf_eq_right.mpr hBC]
  rw [hABC] at hCI
  calc
    A = Z ⊔ (A ⊓ C) := hC
    _ = Z ⊔ ((B ⊓ C) ⊔ (Z ⊓ C)) := by rw [hCI]
    _ = Z ⊔ (B ⊓ C) := by
      rw [← sup_assoc, sup_eq_left.mpr (inf_le_left.trans le_sup_left)]

private theorem finite_frattini_central_supplement (A D Z : Subgroup G)
    [Finite A] (hp : IsPGroup 2 A) (he : IsElementaryAbelian 2 Z)
    (hc : Z ≤ centralizer (A : Set G)) (hA : A = Z ⊔ D) :
    (frattini A).map A.subtype = (frattini D).map D.subtype := by
  have hDA : D ≤ A := hA ▸ le_sup_right
  let : Finite D := Finite.of_injective (inclusion hDA) (inclusion_injective _)
  let : Fact (IsPGroup 2 A) := ⟨hp⟩
  let : Fact (IsPGroup 2 D) := ⟨hp.of_injective (inclusion hDA) (inclusion_injective _)⟩
  let : IsElementaryAbelian 2 Z := he
  apply le_antisymm
  · rw [map_le_iff_le_comap, hp.frattini_eq_closure_squares]
    apply (closure_le (K := ((frattini D).map D.subtype).comap A.subtype)).mpr
    rintro _ ⟨a,rfl⟩
    have hx : (a : G) ∈ (Z : Set G) * (D : Set G) := by
      rw [← coe_mul_of_left_le_normalizer_right Z D
        ((hc.trans (centralizer_le hDA)).trans (Subgroup.centralizer_le_normalizer _)), ← hA]
      exact a.property
    obtain ⟨z,hz,d,hd,heq⟩ := hx
    change (a : G) ^ 2 ∈ (frattini D).map D.subtype
    have hcomm : Commute z d := (hc hz d (hDA hd)).symm
    rw [← heq, hcomm.mul_pow, elemPow_eq_one_of_isElementaryAbelian z hz, one_mul]
    exact mem_map_of_mem D.subtype
      (pth_power_mem_frattini_of_isPGroup (p := 2) (⟨d,hd⟩ : D))
  · have hm := map_mono (f := A.subtype)
      (frattini_map_le_of_isPGroup (p := 2) (inclusion hDA))
    simpa only [map_map, subtype_comp_inclusion] using hm


/-- The opposite-center geometry used in 10.4, before either the Frattini
or D=Z conclusion. The two covers and fixed-space span come from 7.1;
the Sylow products refer to the shifted critical pair. -/
structure BTwoDGeometry (F : Bool → Subgroup G) (t v m w z : Vertex F) where
  previous : (graph F).Adj t v
  middle : (graph F).Adj v m
  terminal : (graph F).Adj m w
  opposite : (graph F).Adj t z
  actor : Subgroup G
  actor_generators : actor = (Z F w ⊔ Z F z) ⊔ Q F v
  factor : ∀ a ∈ stabilizer F v, ∃ l ∈ actor,
    ∃ b ∈ stabilizer F v ⊓ stabilizer F m, a = l*b
  sylow : Sylow 2 (stabilizer F v)
  sylow_le_actor : (sylow : Subgroup (stabilizer F v)).map
    (stabilizer F v).subtype ≤ actor
  cover : D F m t ≤ Z F v ⊔ Q F w
  opposite_cover : D F m t ≤ Z F v ⊔ Q F z
  center_span : Z F v = (Z F v ⊓ Q F w) ⊔ (Z F v ⊓ Q F z)
  separated : D F m t ≤ Q F v
  middle_sylow : Stellmacher.IsSylowSubgroupIn (Z F t ⊔ Q F m) (stabilizer F m)
  previous_sylow : Stellmacher.IsSylowSubgroupIn (Z F m ⊔ Q F t) (stabilizer F t)

variable {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem D_core_normalized (v : Vertex (family P)) :
    stabilizer (family P) v ≤ normalizer (Q (family P) v : Set G) :=
  (stabilizer (family P) v).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))

private theorem D_core_adjacent (h : LocallyRankOneTriple P B)
    {v w : Vertex (family P)} (he : (graph (family P)).Adj v w) : Q (family P) v ≤ stabilizer (family P) w :=
  (source_Z_Q_U h v).2.trans ((ballKernel_one_le_edge (family P) he).trans inf_le_right)

private theorem D_center_core (h : LocallyRankOneTriple P B) (v : Vertex (family P)) :
    Z (family P) v ≤ Q (family P) v := fun _ hz =>
  ((mem_omegaCenterIn_iff _ _).mp ((source_Z_Q_U h v).1 hz)).1

/-- The literal triple intersection occurring in source 10.4(c). -/
def BTwoDGeometry.residual {t v m w z : Vertex (family P)} (_d : BTwoDGeometry (family P) t v m w z) :
    Subgroup G := (D (family P) m t ⊓ Q (family P) w) ⊓ Q (family P) z

variable (h : LocallyRankOneTriple P B)
    (hS : ∀ x, Stellmacher.IsSylowSubgroupIn (Q (family P) x) (U (family P) x))
    (hb : b (family P) = 2) {t v m w z : Vertex (family P)} (d : BTwoDGeometry (family P) t v m w z)

include h hS hb d

private theorem D_contains_center : Z (family P) v ≤ D (family P) m t := by
  exact le_inf (graph_Z_le_Q_of_short h hS
    (by rw [SimpleGraph.dist_eq_one_iff_adj.mpr d.middle,hb]; decide))
    (graph_Z_le_Q_of_short h hS
      (by rw [SimpleGraph.dist_eq_one_iff_adj.mpr d.previous.symm,hb]; decide))

omit hS in
private theorem D_center_stabilizes (x : Vertex (family P)) (he : (graph (family P)).Adj m x) :
    Z (family P) v ≤ stabilizer (family P) x := by
  apply Z_le_stabilizer_of_dist_le_b (family P) h.generate
  have hd := (connected_graph h).dist_triangle (u := v) (v := m) (w := x)
  rw [SimpleGraph.dist_eq_one_iff_adj.mpr d.middle,
    SimpleGraph.dist_eq_one_iff_adj.mpr he] at hd
  rwa [hb]

/-- The natural-center fixed-space span yields the source decomposition
D=R Z. Both covers concern D, not the whole two-core. -/
theorem BTwoDGeometry.decomposition : D (family P) m t = Z (family P) v ⊔ d.residual := by
  have hZD := D_contains_center h hS hb d
  have hZcent := (le_centralizer_iff.mp (graph_Q_centralizes_Z h v)).trans
    (centralizer_le d.separated)
  have hVw := D_center_stabilizes h hb d w d.terminal
  have hVz : Z (family P) v ≤ stabilizer (family P) z := by
    apply Z_le_stabilizer_of_dist_le_b (family P) h.generate
    have hd := (connected_graph h).dist_triangle (u := v) (v := t) (w := z)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr d.previous.symm,
      SimpleGraph.dist_eq_one_iff_adj.mpr d.opposite] at hd
    rwa [hb]
  have hnormw := hVw.trans (D_core_normalized w)
  have hnormz := hVz.trans (D_core_normalized z)
  have hfactor (T : Subgroup G) (hn : Z (family P) v ≤ normalizer (T : Set G))
      (hc : D (family P) m t ≤ Z (family P) v ⊔ T) :
      D (family P) m t ≤ Z (family P) v ⊔ (D (family P) m t ⊓ T) := by
    intro a ha
    have hp : a ∈ (Z (family P) v : Set G) * (T : Set G) := by
      rw [←coe_mul_of_left_le_normalizer_right _ _ hn]
      exact hc ha
    obtain ⟨x,hx,y,hy,rfl⟩ := hp
    have hyD : y ∈ D (family P) m t := by
      simpa only [inv_mul_cancel_left] using
        (D (family P) m t).mul_mem ((D (family P) m t).inv_mem (hZD hx)) ha
    exact (Z (family P) v ⊔ (D (family P) m t ⊓ T)).mul_mem
      (mem_sup_left hx) (mem_sup_right ⟨hyD,hy⟩)
  have hnormal (T : Subgroup G) (hn : Z (family P) v ≤ normalizer (T : Set G)) :
      Z (family P) v ≤ normalizer ((D (family P) m t ⊓ T : Subgroup G) : Set G) :=
    (le_inf (hZD.trans (D (family P) m t).le_normalizer) hn).trans inf_normalizer_le_normalizer_inf
  have hspan : Z (family P) v = (Z (family P) v ⊓ (D (family P) m t ⊓ Q (family P) w)) ⊔
      (Z (family P) v ⊓ (D (family P) m t ⊓ Q (family P) z)) := by
    simpa only [←inf_assoc, inf_of_le_left hZD] using d.center_span
  have he := two_central_supplements (D (family P) m t) (Z (family P) v)
    (D (family P) m t ⊓ Q (family P) w) (D (family P) m t ⊓ Q (family P) z) hZD hZcent
    (hfactor _ hnormw d.cover) (hfactor _ hnormz d.opposite_cover)
    (hnormal _ hnormw) (hnormal _ hnormz) hspan (inf_le_left.trans inf_le_left)
  have hi : (D (family P) m t ⊓ Q (family P) w) ⊓ (D (family P) m t ⊓ Q (family P) z) = d.residual := by
    dsimp [BTwoDGeometry.residual]
    ext x
    simp only [mem_inf]
    tauto
  rwa [hi] at he

omit hS hb in
/-- The residual triple intersection centralizes the two critical center groups. -/
theorem BTwoDGeometry.residual_centralizes :
    d.residual ≤ centralizer ((Z (family P) w ⊔ Z (family P) z : Subgroup G) : Set G) := by
  rw [le_centralizer_iff]
  exact sup_le
    ((le_centralizer_iff.mp (graph_Q_centralizes_Z h w)).trans
      (centralizer_le (inf_le_left.trans inf_le_right : d.residual ≤ Q (family P) w)))
    ((le_centralizer_iff.mp (graph_Q_centralizes_Z h z)).trans
      (centralizer_le (inf_le_right : d.residual ≤ Q (family P) z)))

/-- The two covers imply relative normality of D in the actual local actor. -/
theorem BTwoDGeometry.normalized :
    d.actor ≤ normalizer (D (family P) m t : Set G) := by
  let := finite_endpoints h
  have hZD := D_contains_center h hS hb d
  have hQnorm : Q (family P) v ≤ normalizer (D (family P) m t : Set G) :=
    (le_inf ((D_core_adjacent h d.middle).trans (D_core_normalized m))
      ((D_core_adjacent h d.previous.symm).trans (D_core_normalized t))).trans
        inf_normalizer_le_normalizer_inf
  have hnZ : stabilizer (family P) v ≤ normalizer (Z (family P) v : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer (family P) v)).mp (Z_normal (family P) v)
  have hn (x : Vertex (family P)) (hx : Z (family P) v ≤ stabilizer (family P) x)
      (hx' : Z (family P) x ≤ stabilizer (family P) v) (hc : D (family P) m t ≤ Z (family P) v ⊔ Q (family P) x) :
      Z (family P) x ≤ normalizer (D (family P) m t : Set G) := by
    have hz : Z (family P) v ≤ normalizer (Z (family P) x : Set G) :=
      hx.trans ((normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer (family P) x)).mp (Z_normal (family P) x))
    have he : ⁅Z (family P) v ⊔ Q (family P) x,Z (family P) x⁆ = ⁅Z (family P) v,Z (family P) x⁆ := by
      simpa only [commutator_comm (Z (family P) x) _,sup_comm] using
        (commutator_eq_of_centralizing_sup (B := Q (family P) x ⊔ Z (family P) v) rfl
          (graph_Q_centralizes_Z h x) hz).symm
    exact le_normalizer_iff_commutator_le_left.mpr
      (((commutator_mono hc le_rfl).trans he.le).trans
        ((le_normalizer_iff_commutator_le_left.mp (hx'.trans hnZ)).trans hZD))
  have hdw : (graph (family P)).dist v w ≤ b (family P) := by
    have hd := (connected_graph h).dist_triangle (u := v) (v := m) (w := w)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr d.middle,
      SimpleGraph.dist_eq_one_iff_adj.mpr d.terminal] at hd
    rwa [hb]
  have hdz : (graph (family P)).dist v z ≤ b (family P) := by
    have hd := (connected_graph h).dist_triangle (u := v) (v := t) (w := z)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr d.previous.symm,
      SimpleGraph.dist_eq_one_iff_adj.mpr d.opposite] at hd
    rwa [hb]
  rw [d.actor_generators]
  exact sup_le (sup_le
    (hn w (Z_le_stabilizer_of_dist_le_b (family P) h.generate v w hdw)
      (Z_le_stabilizer_of_dist_le_b (family P) h.generate w v (SimpleGraph.dist_comm ▸ hdw)) d.cover)
    (hn z (Z_le_stabilizer_of_dist_le_b (family P) h.generate v z hdz)
      (Z_le_stabilizer_of_dist_le_b (family P) h.generate z v (SimpleGraph.dist_comm ▸ hdz))
        d.opposite_cover)) hQnorm

/-- The central elementary supplement leaves exactly the same Frattini image. -/
theorem BTwoDGeometry.frattini_residual :
    (frattini (D (family P) m t)).map (D (family P) m t).subtype =
      (frattini d.residual).map d.residual.subtype := by
  let := finite_endpoints h
  let : Finite (D (family P) m t) := Finite.of_injective
    (inclusion (d.separated.trans (Q_le_stabilizer (family P) v))) (inclusion_injective _)
  exact finite_frattini_central_supplement _ _ _
    ((isPGroup_pCoreIn 2 (stabilizer (family P) v)).to_le d.separated)
    (graph_Z_elementary h v)
    ((le_centralizer_iff.mp (graph_Q_centralizes_Z h v)).trans (centralizer_le d.separated))
    (d.decomposition h hS hb)

/-- After the paired Frattini calculation, the literal D is exactly Z. -/
theorem BTwoDGeometry.eq_center (he : IsElementaryAbelian 2 (D (family P) m t)) :
    D (family P) m t = Z (family P) v := by
  let := finite_endpoints h
  let : IsElementaryAbelian 2 (D (family P) m t) := he
  have hR : d.residual ≤ D (family P) m t := inf_le_left.trans inf_le_left
  have hRD : d.residual ≤ centralizer (D (family P) m t : Set G) :=
    hR.trans (commutator_eq_bot_iff_le_centralizer.mp
      (commutator_self_eq_bot_iff.mpr inferInstance))
  have hRm : d.residual ≤ centralizer (Z (family P) m : Set G) :=
    (hR.trans inf_le_left).trans (graph_Q_centralizes_Z h m)
  have hRt : d.residual ≤ centralizer (Z (family P) t : Set G) :=
    (hR.trans inf_le_right).trans (graph_Q_centralizes_Z h t)
  have hspan := bTwo_core_span_of_sylow_products h hS hb d.previous d.middle
    d.middle_sylow d.previous_sylow d.separated
  have hRQ : d.residual ≤ centralizer (Q (family P) v : Set G) := by
    rw [hspan,le_centralizer_iff]
    exact sup_le (sup_le (le_centralizer_iff.mp hRm) (le_centralizer_iff.mp hRt))
      (le_centralizer_iff.mp hRD)
  have hRL : d.residual ≤ centralizer (d.actor : Set G) := by
    rw [d.actor_generators,le_centralizer_iff]
    exact sup_le (le_centralizer_iff.mp (d.residual_centralizes h)) (le_centralizer_iff.mp hRQ)
  have hRZ : d.residual ≤ Z (family P) v := by
    apply le_trans _ (le_iSup (fun T : Sylow 2 (stabilizer (family P) v) =>
      omegaCenterIn ((T : Subgroup (stabilizer (family P) v)).map (stabilizer (family P) v).subtype)) d.sylow)
    intro x hx
    exact (mem_omegaCenterIn_iff _ _).mpr
      ⟨((hR.trans d.separated).trans (pCoreIn_le_sylow _ d.sylow)) hx,
        (hRL.trans (centralizer_le d.sylow_le_actor)) hx,
        elemPow_eq_one_of_isElementaryAbelian x (hR hx)⟩
  rw [d.decomposition h hS hb,sup_eq_left.mpr hRZ]

omit h hS hb d

private theorem frattini_image_mono (A C : Subgroup G) [Finite A] [Finite C]
    (hA : IsPGroup 2 A) (hC : IsPGroup 2 C) (hle : A ≤ C) :
    (frattini A).map A.subtype ≤ (frattini C).map C.subtype := by
  let : Fact (IsPGroup 2 A) := ⟨hA⟩
  let : Fact (IsPGroup 2 C) := ⟨hC⟩
  have he := map_mono (f := C.subtype)
    (frattini_map_le_of_isPGroup (p := 2) (inclusion hle))
  simpa only [map_map,subtype_comp_inclusion] using he

include h hS hb

/-- The two literal residuals lie in the opposite D. Their Frattini
images therefore coincide, and relative normality in the two local actors
kills this common subgroup by faithfulness. -/
theorem bTwo_paired_D_frattini {t v m w z₀ z₁ : Vertex (family P)}
    (d₀ : BTwoDGeometry (family P) t v m w z₀)
    (d₁ : BTwoDGeometry (family P) w m v t z₁) :
    (frattini (D (family P) m t)).map (D (family P) m t).subtype = ⊥ ∧
      (frattini (D (family P) v w)).map (D (family P) v w).subtype = ⊥ := by
  let := finite_endpoints h
  let D₀ := D (family P) m t
  let D₁ := D (family P) v w
  have hp₀ : IsPGroup 2 D₀ :=
    (isPGroup_pCoreIn 2 (stabilizer (family P) v)).to_le d₀.separated
  have hp₁ : IsPGroup 2 D₁ :=
    (isPGroup_pCoreIn 2 (stabilizer (family P) m)).to_le d₁.separated
  let : Finite D₀ := Finite.of_injective
    (inclusion (d₀.separated.trans (Q_le_stabilizer (family P) v))) (inclusion_injective _)
  let : Finite D₁ := Finite.of_injective
    (inclusion (d₁.separated.trans (Q_le_stabilizer (family P) m))) (inclusion_injective _)
  have hR₀ : d₀.residual ≤ D₀ := inf_le_left.trans inf_le_left
  have hR₁ : d₁.residual ≤ D₁ := inf_le_left.trans inf_le_left
  let : Finite d₀.residual := Finite.of_injective (inclusion hR₀) (inclusion_injective _)
  let : Finite d₁.residual := Finite.of_injective (inclusion hR₁) (inclusion_injective _)
  have hcross₀ : d₀.residual ≤ D₁ :=
    le_inf (hR₀.trans d₀.separated) (inf_le_left.trans inf_le_right)
  have hcross₁ : d₁.residual ≤ D₀ :=
    le_inf (hR₁.trans d₁.separated) (inf_le_left.trans inf_le_right)
  have he : (frattini D₀).map D₀.subtype = (frattini D₁).map D₁.subtype := by
    apply le_antisymm
    · rw [d₀.frattini_residual h hS hb]
      exact frattini_image_mono _ _ (hp₀.to_le hR₀) hp₁ hcross₀
    · rw [d₁.frattini_residual h hS hb]
      exact frattini_image_mono _ _ (hp₁.to_le hR₁) hp₀ hcross₁
  have hbot : (frattini D₀).map D₀.subtype = ⊥ := by
    apply graph_local_common_normal_eq_bot h d₀.middle d₀.actor d₁.actor _ d₀.factor
    · intro a ha
      obtain ⟨l,hl,b,hb,hab⟩ := d₁.factor a ha
      exact ⟨l,hl,b,⟨hb.2,hb.1⟩,hab⟩
    · exact (map_subtype_le _).trans (le_inf
        (d₀.separated.trans (Q_le_stabilizer (family P) v))
        (inf_le_left.trans (Q_le_stabilizer (family P) m)))
    · exact (d₀.normalized h hS hb).trans
        (normalizer_le_normalizer_characteristic_image D₀ (frattini D₀))
    · rw [he]
      exact (d₁.normalized h hS hb).trans
        (normalizer_le_normalizer_characteristic_image D₁ (frattini D₁))
  exact ⟨hbot,he.symm.trans hbot⟩

/-- Both D identities in the noncentral b=2 branch, from the paired
opposite-center geometry. Neither identity is a premise. -/
theorem bTwo_paired_D_eq_centers {t v m w z₀ z₁ : Vertex (family P)}
    (d₀ : BTwoDGeometry (family P) t v m w z₀)
    (d₁ : BTwoDGeometry (family P) w m v t z₁) :
    D (family P) m t = Z (family P) v ∧ D (family P) v w = Z (family P) m := by
  let := finite_endpoints h
  obtain ⟨h₀,h₁⟩ := bTwo_paired_D_frattini h hS hb d₀ d₁
  have elementary {t v m w z : Vertex (family P)}
      (c : BTwoDGeometry (family P) t v m w z)
      (hphi : (frattini (D (family P) m t)).map (D (family P) m t).subtype = ⊥) :
      IsElementaryAbelian 2 (D (family P) m t) := by
    let : Finite (D (family P) m t) := Finite.of_injective
      (inclusion (c.separated.trans (Q_le_stabilizer (family P) v))) (inclusion_injective _)
    let : Fact (IsPGroup 2 (D (family P) m t)) :=
      ⟨(isPGroup_pCoreIn 2 (stabilizer (family P) v)).to_le c.separated⟩
    exact (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp
      ((map_eq_bot_iff_of_injective _ (D (family P) m t).subtype_injective).mp hphi)
  exact ⟨d₀.eq_center h hS hb (elementary d₀ h₀),
    d₁.eq_center h hS hb (elementary d₁ h₁)⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
