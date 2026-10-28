module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoBinaryMaximum
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoBinaryPathMinimum

/-!
# Exact binary exceptional source path parameters

The two actual completions of the fully marked binary amalgam have the same
regular nonbacktracking path lengths through their common universal cover.
Transporting the native regular six-path and the universal upper bound gives
the maximum six. The proved source minimum five makes the lower witness
simple. The upper bound also includes the book's permitted closed paths:
except for a length-two return, these source paths are nonbacktracking.

The original critical-pair consumer combines this binary calculation with the
completed field-four calculation. Exhaustive selection supplies the actual
marked comparison, so no model or path premise is added to that consumer.
The original opposite-core equality `hD` remains explicit; its discharge and
the remaining regular Chapter 10 branch are separate retained obligations.
The existing full original and reduced endpoint/Borel markings are preserved.

The cover comparison is proved at an abstract completion boundary before
specialization, avoiding expensive unfolding of the concrete parabolics.
Source: Delgado–Goldschmidt–Stellmacher, *Groups and Graphs* (1985),
path convention p.60, extrema pp.73–74, and (10.9), printed pp.162–163.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup SimpleGraph SimpleGraph.Walk SimpleGraph.BasedWalk
open SimpleGraph.PathTransitivePolygon Theory.GroupAction.CubicTree
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.WeakBNPair.RegularTree
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
open DGS85.Reduction OriginalExtension Atlas.G2 Atlas.G2.BinaryParabolicPair
namespace BinaryMaximumSource
local notation "MF" => BinaryPaths.family

universe u v w
private theorem completion_regular_iff
    {A B C : Type u} {X : Type v} {Y : Type w} [Group A] [Group B] [Group C] [Group X] [Group Y]
    (am : RankTwoAmalgam A B C)
    (c : FaithfulCompletion am (G := X)) (d : FaithfulCompletion am (G := Y))
    (hc : c.left.range ⊓ c.right.range = c.middle.range)
    (hd : d.left.range ⊓ d.right.range = d.middle.range) (i : Bool) (n : ℕ) :
    (∃ p : BasedWalk (graph (FaithfulCompletion.cosetFamily (G := X) c)) n
        (base (FaithfulCompletion.cosetFamily (G := X) c) i),
      p.Nonbacktracking ∧ Regular (A := X) p) ↔
    (∃ p : BasedWalk (graph (FaithfulCompletion.cosetFamily (G := Y) d)) n
        (base (FaithfulCompletion.cosetFamily (G := Y) d) i),
      p.Nonbacktracking ∧ Regular (A := Y) p) := by
  have h1 := (Universal.coverData_of_overlap am c hc).exists_regular_path_iff n
    (base (Universal.cosetFamily am) i)
  have h2 := (Universal.coverData_of_overlap am d hd).exists_regular_path_iff n
    (base (Universal.cosetFamily am) i)
  exact h1.trans h2.symm


private theorem pair_generate : derivedFirst ⊔ derivedSecond = ⊤ := by
  apply map_injective (f := DerivedModel.subtype) DerivedModel.subtype_injective
  rw [Subgroup.map_sup,derivedFirst_map_subtype,derivedSecond_map_subtype,
    ←MonoidHom.range_eq_map,DerivedModel.range_subtype]
  have h := DerivedParabolicGeneration.binary_restricted_pair_generate
  rw [LieParabolicSetup.parabolic₁_binary] at h
  exact h

private def mc : FaithfulCompletion derivedAmalgam (G := DerivedModel) :=
  FaithfulCompletion.ofSubgroups derivedFirst (derivedSylow : Subgroup DerivedModel)
    derivedSecond derivedSylow_le_first derivedSylow_le_second pair_generate

private theorem mc_family : mc.cosetFamily = BinaryPaths.family := by
  funext i
  cases i <;> simp [FaithfulCompletion.cosetFamily,mc,BinaryPaths.family]

private theorem mc_overlap : mc.left.range ⊓ mc.right.range = mc.middle.range := by
  have hl : mc.left.range = derivedFirst := Subgroup.range_subtype _
  have hr : mc.right.range = derivedSecond := Subgroup.range_subtype _
  have hm : mc.middle.range = (derivedSylow : Subgroup DerivedModel) := by
    ext x
    constructor
    · rintro ⟨d,rfl⟩; exact d.property
    · intro hx; exact ⟨⟨x,hx⟩,rfl⟩
  rw [hl,hr,hm]
  exact derived_parabolic_intersection_in_model

variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
private theorem endpoint_le (h : HypothesisF11 L S) (i : Fin 2) :
    parabolic L (SuzukiContainment.reducedSylow L S) i ≤ G₀ L S := by
  rw [← P₀_eq_source h i]
  fin_cases i
  · exact le_sup_left
  · exact le_sup_right

private noncomputable def completionOfSubgroups (A D C H : Subgroup G)
    (hDA : D ≤ A) (hDC : D ≤ C) (hA : A ≤ H) (hC : C ≤ H) (hgen : A ⊔ C = H) :
    FaithfulCompletion (RankTwoAmalgam.ofSubgroups A D C hDA hDC) (G := H) where
  left := inclusion hA
  right := inclusion hC
  compatible := rfl
  left_injective := inclusion_injective _
  right_injective := inclusion_injective _
  middle_injective := fun _ _ hxy => Subtype.ext (congrArg (fun x : H => (x : G)) hxy)
  generated := by
    rw [inclusion_range, inclusion_range, ← subgroupOf_sup hA hC, hgen]
    exact subgroupOf_self _

private theorem completionOfSubgroups_overlap (A D C H : Subgroup G)
    (hDA : D ≤ A) (hDC : D ≤ C) (hA : A ≤ H) (hC : C ≤ H) (hgen : A ⊔ C = H)
    (hinter : A ⊓ C = D) :
    (completionOfSubgroups A D C H hDA hDC hA hC hgen).left.range ⊓
      (completionOfSubgroups A D C H hDA hDC hA hC hgen).right.range =
      (completionOfSubgroups A D C H hDA hDC hA hC hgen).middle.range := by
  change (inclusion hA).range ⊓ (inclusion hC).range = (inclusion (hDA.trans hA)).range
  rw [inclusion_range, inclusion_range, inclusion_range]
  change (A ⊓ C).subgroupOf H = D.subgroupOf H
  rw [hinter]

private noncomputable def sc (h : HypothesisF11 L S) :
    FaithfulCompletion (reducedAmalgam L S) (G := G₀ L S) :=
  completionOfSubgroups _ _ _ _ (commonBorel_le_parabolic 0) (commonBorel_le_parabolic 1)
    (endpoint_le h 0) (endpoint_le h 1)
    (by rw [← P₀_eq_source h 0, ← P₀_eq_source h 1]; rfl)

private theorem sc_family (h : HypothesisF11 L S) :
    (sc h).cosetFamily = reducedFamily L S := by
  funext i
  cases i
  · change (inclusion (endpoint_le h 0)).range = (P₀ L S 0).subgroupOf (G₀ L S)
    rw [inclusion_range,P₀_eq_source h 0]
  · change (inclusion (endpoint_le h 1)).range = (P₀ L S 1).subgroupOf (G₀ L S)
    rw [inclusion_range,P₀_eq_source h 1]

private theorem sc_overlap (h : HypothesisF11 L S) :
    (sc h).left.range ⊓ (sc h).right.range = (sc h).middle.range := by
  exact completionOfSubgroups_overlap _ _ _ _
    (commonBorel_le_parabolic 0) (commonBorel_le_parabolic 1)
    (endpoint_le h 0) (endpoint_le h 1)
    (by rw [← P₀_eq_source h 0, ← P₀_eq_source h 1]; rfl)
    (lemma_F_1_3_6 (SuzukiContainment.reduced_hypothesis h))


local notation "F₀" => reducedFamily L S
local notation "α" => base F₀ false
private theorem regular_graphIso {X Y A : Type*} [Group A]
    [MulAction A X] [MulAction A Y] {Γ : SimpleGraph X} {Δ : SimpleGraph Y}
    (e : Γ ≃g Δ) (he : ∀ (a : A) v, e (a • v) = a • e v)
    {n : ℕ} {v : X} (p : BasedWalk Γ n v) (hp : Regular (A := A) p) :
    Regular (A := A) (p.map e.toHom) := by
  refine ⟨(rightRegular_reverse_iff _).mp ?_,(rightRegular_graphIso_iff e he p).mpr hp.2⟩
  have hh := (rightRegular_graphIso_iff e he (reverse p)).mpr
    ((rightRegular_reverse_iff p).mpr hp.1)
  apply rightRegular_of_vertices_eq _ _ _ hh
  simp only [BasedWalk.vertices_map,vertices_reverse,List.map_reverse]

/-- The compatible marked comparison transports regular paths at the
source alpha root through the actual common coset covers. -/
theorem marked_regular_transfer (h : HypothesisF11 L S)
    (e : Iso (reducedAmalgam L S).reverse derivedAmalgam)
    (n : ℕ) (ht : ∃ p : BasedWalk (graph MF) n (base MF true),
      p.Nonbacktracking ∧ Regular (A := DerivedModel) p) :
    ∃ p : BasedWalk (graph F₀) n α,
      p.Nonbacktracking ∧ Regular (A := G₀ L S) p := by
  let d : FaithfulCompletion (reducedAmalgam L S) (G := DerivedModel) :=
    mc.reverse.comapIso e.reverse
  have hd : d.left.range ⊓ d.right.range = d.middle.range := by
    change (mc.reverse.comapIso e.reverse).left.range ⊓
      (mc.reverse.comapIso e.reverse).right.range =
      (mc.reverse.comapIso e.reverse).middle.range
    rw [FaithfulCompletion.comapIso_left_range,
      FaithfulCompletion.comapIso_right_range,
      FaithfulCompletion.comapIso_middle_range]
    exact mc.reverse_overlap mc_overlap
  have hf : d.cosetFamily = swapFamily MF := by
    funext i
    cases i
    · change (mc.reverse.comapIso e.reverse).left.range = MF true
      rw [FaithfulCompletion.comapIso_left_range, FaithfulCompletion.reverse_left]
      exact congrFun mc_family true
    · change (mc.reverse.comapIso e.reverse).right.range = MF false
      rw [FaithfulCompletion.comapIso_right_range, FaithfulCompletion.reverse_right]
      exact congrFun mc_family false
  have hm : ∃ p : BasedWalk (graph d.cosetFamily) n (base d.cosetFamily false),
      p.Nonbacktracking ∧ Regular (A := DerivedModel) p := by
    rw [hf]
    obtain ⟨p,hp,hr⟩ := ht
    have hbase : swapGraphIso MF (base MF true) = base (swapFamily MF) false := rfl
    rw [←hbase]
    exact ⟨p.map (swapGraphIso MF).toHom,
      (BasedWalk.nonbacktracking_map_iff (swapGraphIso MF).toHom
        (fun v => ((swapGraphIso MF).mapNeighborSet v).injective) p).mpr hp,
      regular_graphIso (swapGraphIso MF) (swapVertex_smul MF) p hr⟩
  have hh := (completion_regular_iff (reducedAmalgam L S) d (sc h)
    hd (sc_overlap h) false n).mp hm
  rw [sc_family h] at hh
  exact hh

/-- The universal covers used for the marked lower witness also transport
nonexistence of longer regular paths, at both roots and every base vertex. -/
theorem marked_regular_length_le_six (h : HypothesisF11 L S)
    (e : Iso (reducedAmalgam L S).reverse derivedAmalgam)
    {n : ℕ} {v : Vertex F₀} (p : BasedWalk (graph F₀) n v)
    (hp : p.Nonbacktracking) (hr : Regular (A := G₀ L S) p) : n ≤ 6 := by
  let d : FaithfulCompletion (reducedAmalgam L S) (G := DerivedModel) :=
    mc.reverse.comapIso e.reverse
  have hd : d.left.range ⊓ d.right.range = d.middle.range := by
    change (mc.reverse.comapIso e.reverse).left.range ⊓
      (mc.reverse.comapIso e.reverse).right.range =
      (mc.reverse.comapIso e.reverse).middle.range
    rw [FaithfulCompletion.comapIso_left_range,
      FaithfulCompletion.comapIso_right_range,
      FaithfulCompletion.comapIso_middle_range]
    exact mc.reverse_overlap mc_overlap
  have hf : d.cosetFamily = swapFamily MF := by
    funext i
    cases i
    · change (mc.reverse.comapIso e.reverse).left.range = MF true
      rw [FaithfulCompletion.comapIso_left_range,FaithfulCompletion.reverse_left]
      exact congrFun mc_family true
    · change (mc.reverse.comapIso e.reverse).right.range = MF false
      rw [FaithfulCompletion.comapIso_right_range,FaithfulCompletion.reverse_right]
      exact congrFun mc_family false
  obtain ⟨q,hq,g,hg⟩ := exists_base_path_translate F₀ rfl p hp
  have hrev : p.vertices.map (g⁻¹ • ·) = q.vertices := by
    rw [←hg,List.map_map]
    simp only [Function.comp_def,inv_smul_smul]
    exact List.map_id _
  have hact : GraphAction (graph F₀) (G₀ L S) :=
    ⟨fun a _ _ ha => (Subgroup.CosetGeometry.translationGraphIso F₀ a).toHom.map_adj ha⟩
  have hqr : Regular (A := G₀ L S) q :=
    ⟨leftRegular_of_conjugate hact p q g⁻¹ hrev hr.1,
      rightRegular_of_conjugate hact p q g⁻¹ hrev hr.2⟩
  have hs : ∃ q : BasedWalk (graph (sc h).cosetFamily) n
      (base (sc h).cosetFamily v.type),
      q.Nonbacktracking ∧ Regular (A := G₀ L S) q := by
    rw [sc_family h]
    exact ⟨q,hq,hqr⟩
  have hm := (completion_regular_iff (reducedAmalgam L S) (sc h) d
    (sc_overlap h) hd v.type n).mp hs
  rw [hf] at hm
  obtain ⟨r,hrnb,hrr⟩ := hm
  let t := r.map (swapGraphIso MF).symm.toHom
  have ht : t.Nonbacktracking :=
    (BasedWalk.nonbacktracking_map_iff (swapGraphIso MF).symm.toHom
      (fun v => ((swapGraphIso MF).symm.mapNeighborSet v).injective) r).mpr hrnb
  have htr : Regular (A := DerivedModel) t := regular_graphIso (swapGraphIso MF).symm
    (by intro a v; rcases v with ⟨i,v⟩; cases i <;> rfl) r hrr
  exact BinaryMaximum.regular_length_le_six t ht htr

variable {P : Fin 2 → Subgroup G}
private theorem based_penultimate {V : Type*} {Γ : SimpleGraph V} {a b c : V}
    (hab : Γ.Adj a b) (p : Γ.Walk b c) :
    (ofWalk (Walk.cons hab p)).penultimate = (Walk.cons hab p).penultimate := by
  induction p generalizing a with
  | nil => rfl
  | cons h p ih => exact ih h

private theorem forward_ofWalk {V : Type*} {Γ : SimpleGraph V} {a b z : V}
    (p : Γ.Walk a b) : Theory.GroupAction.CubicTree.Forward (ofWalk p) z ↔
      Γ.Adj b z ∧ z ≠ p.penultimate := by
  cases p with
  | nil =>
    change Γ.Adj a z ↔ Γ.Adj a z ∧ z ≠ a
    exact ⟨fun hz => ⟨hz,hz.ne.symm⟩,And.left⟩
  | cons hab p =>
    change (Γ.Adj (ofWalk (Walk.cons hab p)).endpoint z ∧
      z ≠ (ofWalk (Walk.cons hab p)).penultimate) ↔ _
    rw [endpoint_ofWalk,based_penultimate]

private theorem nb_ofWalk_iff {V : Type*} {Γ : SimpleGraph V} {a b : V} (p : Γ.Walk a b) :
    (ofWalk p).Nonbacktracking ↔ ∀ i, i+2 ≤ p.length → p.getVert i ≠ p.getVert (i+2) := by
  induction p with
  | nil =>
    constructor
    · intro _ i hi; simp only [length_nil] at hi; omega
    · intro _; trivial
  | @cons a b c hab p ih =>
    cases p with
    | nil =>
      constructor
      · intro _ i hi; simp only [length_cons,length_nil] at hi; omega
      · intro _; trivial
    | @cons b d c hbd p =>
      change (d ≠ a ∧ (ofWalk (Walk.cons hbd p)).Nonbacktracking) ↔ _
      rw [ih]
      constructor
      · rintro ⟨hne,hp⟩ i hi
        cases i with
        | zero => simpa only [getVert_zero,getVert_cons_succ] using hne.symm
        | succ i => exact hp i (by simp only [length_cons] at *; omega)
      · intro hp
        refine ⟨by simpa only [getVert_zero,getVert_cons_succ] using
          (hp 0 (by simp only [length_cons]; omega)).symm,?_⟩
        intro i hi
        exact hp (i+1) (by simp only [length_cons] at *; omega)

private theorem sourcePath_nonbacktracking {a b : Vertex (family P)} (p : (graph (family P)).Walk a b)
    (hp : IsSourcePath p) (hne : p.length ≠ 2) : (ofWalk p).Nonbacktracking := by
  rcases hp with hp | ⟨hab,hp⟩
  · exact nonbacktracking_ofWalk_of_isPath p hp
  · subst b
    rw [nb_ofWalk_iff]
    intro i hi he
    by_cases hlt : i+2 < p.length
    · have h1 : i ≤ p.dropLast.length := by rw [length_dropLast]; omega
      have h2 : i+2 ≤ p.dropLast.length := by rw [length_dropLast]; omega
      have hh := hp.getVert_injOn h1 h2
        (by rwa [getVert_dropLast (by omega : i < p.length), getVert_dropLast hlt])
      omega
    · have hlast : i+2 = p.length := by omega
      have h1 : i ≤ p.dropLast.length := by rw [length_dropLast]; omega
      have hh := hp.getVert_injOn h1 (Nat.zero_le _) (by
        rw [getVert_dropLast (by omega : i < p.length),getVert_zero]
        rwa [hlast,getVert_length] at he)
      omega


private theorem fixer_support {a b : Vertex (family P)}
    (p : (graph (family P)).Walk a b) (g : G) :
    g ∈ pathFixer (X := G) p ↔ ∀ z ∈ p.support, g • z = z := by
  constructor
  · intro hg z hz
    obtain ⟨k,rfl,hk⟩ := mem_support_iff_exists_getVert.mp hz
    exact hg k hk
  · intro hg k _
    exact hg _ (p.getVert_mem_support k)

private theorem rightRegular_vertices {n k : ℕ} {a b : Vertex (family P)}
    (p : BasedWalk (graph (family P)) n a) (q : BasedWalk (graph (family P)) k b)
    (he : p.vertices = q.vertices) : RightRegular (A := G) p ↔ RightRegular (A := G) q := by
  have hn : n = k := by
    have hh := congrArg List.length he
    simp only [BasedWalk.length_vertices] at hh
    omega
  subst k
  exact ⟨rightRegular_of_vertices_eq p q he,rightRegular_of_vertices_eq q p he.symm⟩

private theorem exit_regular_iff {a b : Vertex (family P)}
    (p : (graph (family P)).Walk a b) :
    PathExitTransitive p ↔ RightRegular (A := G) (ofWalk p) := by
  constructor
  · intro hr z w hz hw
    obtain ⟨g,hg,he⟩ := hr z ((forward_ofWalk p).mp hz) w ((forward_ofWalk p).mp hw)
    exact ⟨g,fun y hy => (fixer_support p g).mp hg y
      (by rwa [vertices_ofWalk] at hy),he⟩
  · intro hr z hz w hw
    obtain ⟨g,hg,he⟩ := hr z w ((forward_ofWalk p).mpr hz) ((forward_ofWalk p).mpr hw)
    exact ⟨g,(fixer_support p g).mpr (fun y hy => hg y
      (by rwa [vertices_ofWalk])),he⟩

private theorem walk_regular_iff {a b : Vertex (family P)}
    (p : (graph (family P)).Walk a b) :
    PathRegular p ↔ Regular (A := G) (ofWalk p) := by
  have he : (ofWalk p.reverse).vertices = (reverse (ofWalk p)).vertices := by
    rw [vertices_ofWalk,Walk.support_reverse,vertices_reverse,vertices_ofWalk]
  have hr : RightRegular (A := G) (ofWalk p.reverse) ↔
      RightRegular (A := G) (reverse (ofWalk p)) :=
    rightRegular_vertices _ _ he
  rw [PathRegular,exit_regular_iff,exit_regular_iff,hr,rightRegular_reverse_iff]
  exact and_comm


private theorem regular_six_isPath (h : HypothesisF11 L S)
    (hs : DGS85.sourceS (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) = 5)
    {v : Vertex F₀} (p : BasedWalk (graph F₀) 6 v)
    (hp : p.Nonbacktracking) (hr : Regular (A := G₀ L S) p) : p.toWalk.IsPath := by
  have hval (x : Vertex F₀) : 3 ≤ Nat.card ((graph F₀).neighborSet x) := by
    rw [card_neighbors_of_indices F₀
      (fun i => ((F₀ (!i)).subgroupOf (F₀ i)).index) (fun _ => rfl)]
    exact source_valence_ge_three (reduced_triple h) (reduced_vertex_sylow h) x.type
  have hsimp {x : Vertex F₀} (q : BasedWalk (graph F₀) 5 x)
      (hq : q.Nonbacktracking) : q.vertices.Nodup := by
    have hqpath := isPath_of_short_rightRegular hval 5
      (fun n hn x r hr => (sourceS_short_regular (reduced_triple h)
        (reduced_vertex_sylow h) r (by omega) hr).2) q le_rfl hq
    rw [← support_toWalk]
    exact hqpath.support_nodup
  have hpre := hsimp (p.take 5 (by decide)) (nonbacktracking_take _ p hp)
  have htail := hsimp p.2 (nonbacktracking_tail p hp)
  rcases p with ⟨a,b,c,d,e,f,z⟩
  change [v,(a : Vertex F₀),b,c,d,e].Nodup at hpre
  change [(a : Vertex F₀),b,c,d,e,f].Nodup at htail
  have hfv : (f : Vertex F₀) ≠ v := by
    intro he
    have hae : (a : Vertex F₀) ≠ (e : Vertex F₀) := by
      have hh := (List.nodup_cons.mp (List.nodup_cons.mp hpre).2).1
      intro heq
      apply hh
      simp [heq]
    have hfwd : Forward (Γ := graph F₀) (n := 6) (x := v)
        (⟨a,b,c,d,e,f,z⟩ : BasedWalk (graph F₀) 6 v) a := by
      change (graph F₀).Adj f a ∧ (a : Vertex F₀) ≠ (e : Vertex F₀)
      exact ⟨by rw [he]; exact a.property,hae⟩
    exact forward_not_mem_vertices_of_rightRegular hval _ hr.2 hfwd (by
      change (a : Vertex F₀) ∈ [v,a,b,c,d,e,f]
      simp)
  apply Walk.IsPath.mk'
  change [v,(a : Vertex F₀),b,c,d,e,f].Nodup
  refine List.nodup_cons.mpr ⟨?_,htail⟩
  have hh := (List.nodup_cons.mp hpre).1
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hh ⊢
  exact ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1,hh.2.2.2.2,hfv.symm⟩

private theorem six_source_regular {v : Vertex F₀}
    (p : BasedWalk (graph F₀) 6 v) (hr : Regular (A := G₀ L S) p) :
    PathRegular p.toWalk := by
  rcases p with ⟨a,b,c,d,e,f,z⟩
  constructor
  · intro x hx y hy
    obtain ⟨g,hg,hgy⟩ := hr.2 x y hx hy
    refine ⟨g,?_,hgy⟩
    intro i hi
    apply hg
    rw [←support_toWalk]
    exact Walk.getVert_mem_support _ i
  · intro x hx y hy
    have hx' : Backward (Γ := graph F₀) (n := 6) (x := v)
        (⟨a,b,c,d,e,f,z⟩ : BasedWalk (graph F₀) 6 v) x := by
      exact hx
    have hy' : Backward (Γ := graph F₀) (n := 6) (x := v)
        (⟨a,b,c,d,e,f,z⟩ : BasedWalk (graph F₀) 6 v) y := by
      exact hy
    obtain ⟨g,hg,hgy⟩ := hr.1 x y hx' hy'
    refine ⟨g,?_,hgy⟩
    intro i hi
    apply hg
    rw [←support_toWalk]
    have hh := Walk.getVert_mem_support
      (BasedWalk.toWalk (G := graph F₀) (n := 6) (x := v) ⟨a,b,c,d,e,f,z⟩).reverse i
    simpa only [Walk.support_reverse,List.mem_reverse] using hh


/-- The compatible binary marking supplies both literal source extrema,
including the permitted closed source paths. -/
theorem path_parameters (h : HypothesisF11 L S)
    (e : Iso (reducedAmalgam L S).reverse derivedAmalgam) :
    HasSourcePathParameters
      (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 6 5 := by
  have hs := BinaryMinimum.sourceS_eq_five h e
  obtain ⟨p,hp,hr⟩ := marked_regular_transfer h e 6
    ⟨BinaryPaths.sixPath,BinaryPaths.sixPath_nb,BinaryMaximum.sixPath_regular⟩
  constructor
  · refine ⟨⟨α,p.endpoint,p.toWalk,Or.inl (regular_six_isPath h hs p hp hr),
      length_toWalk p,six_source_regular p hr⟩,?_⟩
    rintro n ⟨a,b,q,hq,hql,hqr⟩
    by_cases hn : n ≤ 6
    · exact hn
    · have hnb := sourcePath_nonbacktracking q hq (by omega)
      have hh := marked_regular_length_le_six h e (ofWalk q) hnb
        ((walk_regular_iff q).mp hqr)
      omega
  · have hh := (sourceS_spec (reduced_triple h) (reduced_vertex_sylow h)).2
    rw [hs] at hh
    exact hh
end BinaryMaximumSource

open Noncommuting
open scoped Pointwise commutatorElement MatrixGroups
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F₀" => reducedFamily L S
local notation "α" => base F₀ false
local notation "β" => base F₀ true
/-- DGS (10.9): exhaustive exceptional selection supplies r = 6 and s = 5
in both the binary and field-four rows. The original opposite-core equality
is retained, together with the fully marked original source assumptions. -/
theorem original_bTwo_exceptional_path_parameters
    (h : HypothesisF11 L S) {u t : Vertex F₀}
    (hc : IsCriticalPair F₀ α u) (hne : ⁅Z F₀ α,Z F₀ u⁆ ≠ ⊥)
    (hb : b F₀ = 2) (hβu : (graph F₀).Adj β u)
    (ht : (graph F₀).Adj α t) (htne : t ≠ β)
    (hD : (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map (G₀ L S).subtype =
      (Z F₀ α).map (G₀ L S).subtype) :
    HasSourcePathParameters
      (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 6 5 := by
  rcases original_bTwo_exceptional_marked_selection h hc hne hb hβu ht htne hD with
    ⟨_,_,_,_,_,_,_,⟨eG⟩⟩ | ⟨_,_,_,_,_,_,_,hp⟩
  · exact BinaryMaximumSource.path_parameters h eG
  · exact hp
end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
