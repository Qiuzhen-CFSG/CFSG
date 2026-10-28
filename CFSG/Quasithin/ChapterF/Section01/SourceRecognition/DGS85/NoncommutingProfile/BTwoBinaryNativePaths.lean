module
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.StandardPair
public import Theory.GroupAction.RankTwoCosetGeometry.PathOrderLowerBound
public import Theory.GroupAction.RankTwoCosetGeometry.PathCardinality
public import Theory.GroupAction.RankTwoCosetGeometry.AlternatingFive
public import Theory.Combinatorics.SimpleGraph.NonbacktrackingCount
public import Theory.GroupAction.CubicTree.ArcReversal
public import Theory.GroupAction.RankTwoCosetGeometry.PathKernelTransport

/-!
# Native binary exceptional five-path transitivity

The two existing cubic actors give a nonbacktracking five-path in the coset
geometry of the actual G₂(2)′ parabolics. Every fixer lies in the order-32
Borel and centralizes the terminal conjugate of the distinguished root
involution. Three matrix entries, checked in the Lean kernel on the binary
root coordinates, leave only two possible elements. The root stabilizer has
order 96 and there are 48 five-paths, so orbit–stabilizer proves transitivity.
Reversal gives the other orientation.

The nonidentity survivor also fixes the displayed six-path. There are 96
six-paths from its root, so that stabilizer cannot be transitive on them.
These are the two native inputs for the literal source minimum s = 5;
no maximum-regular-length assertion is made here.

Source: Delgado–Goldschmidt–Stellmacher, *Groups and Graphs* (1985),
(10.9), printed p.163. Root and octonion conventions are inherited from the
licensed ATLAS imports; see `LICENSES/ATLAS.txt`.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.BinaryPaths
open Atlas.G2 Atlas.G2.Explicit Atlas.G2.BinaryCore Atlas.G2.BinaryParabolicPair
open Subgroup.CosetGeometry.RankTwo
open SimpleGraph SimpleGraph.PathTransitivePolygon
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def family : Bool → Subgroup DerivedModel := fun i => if i then derivedSecond else derivedFirst

def a : DerivedModel := ⟨movingActor,movingActor_mem_derived⟩
def b : DerivedModel := ⟨cubicActor,cubicActor_mem_derived⟩

theorem a_mem : a ∈ family true := movingActor_mem_derivedSecond
theorem b_mem : b ∈ family false := cubicActor_mem_derivedFirst

theorem a_not_mem : a ∉ family false := by
  intro h
  have he := firstParabolic_centralizes_z movingActor h
  exact movingActor_moves (by rw [he]; simp)

theorem b_not_mem : b ∉ family true := by
  intro h
  have hm := (show secondParabolic ≤ pointStabilizer (K := ZMod 2) from
    parabolic_eq_pointStabilizer.le) h
  change cubicActor ∈ pointStabilizer at hm
  obtain ⟨u,hu⟩ := (mem_pointStabilizer_iff cubicActor).mp hm
  have he := congrFun hu 1
  have hv : cubicActor.val (Atlas.SplitOctonion.basisVector 0) 1 = 1 := by decide +kernel
  rw [hv] at he
  simp [Atlas.SplitOctonion.basisVector] at he

def path : BasedWalk (graph family) 5 (base family true) :=
  alternatingFive family true a b a_mem b_mem

theorem path_nb : path.Nonbacktracking :=
  alternatingFive_nonbacktracking family true a b a_mem b_mem a_not_mem b_not_mem

theorem family_inf (i : Bool) : family i ⊓ family (!i) = (derivedSylow : Subgroup DerivedModel) := by
  cases i
  · exact derived_parabolic_intersection_in_model
  · exact (inf_comm _ _).trans derived_parabolic_intersection_in_model

def longWord : Model (ZMod 2) := cubicActor * movingActor * cubicActor * movingActor

def terminalZ : Model (ZMod 2) := longWord * z * longWord⁻¹

private theorem derived_parameters (t : Fin 6 → ZMod 2) :
    unipotentProduct t ∈ DerivedModel ↔ t 2 + t 3 + t 5 = 0 := by
  change unipotentProduct t ∈ commutator (Model (ZMod 2)) ↔ _
  rw [commutator_eq_longRootClosure, ← QuotientGroup.eq_one_iff]
  change BinaryException.projection (unipotentProduct t) = 1 ↔ _
  simp only [unipotentProduct, map_mul, BinaryException.project_A,
    BinaryException.project_B, BinaryException.project_E, one_mul, mul_one,
    BinaryException.project_C_eq_D, BinaryException.project_D_eq_F]
  rw [← map_mul, ← map_mul, Atlas.G2.rootF_add, Atlas.G2.rootF_add]
  have hb : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide +kernel
  rcases hb (t 2 + t 3 + t 5) with h | h
  · simp [h, rootF_zero]
  · rw [h]
    exact iff_of_false quotientBit_ne_one (by decide)

private theorem surviving_parameters : ∀ t : Fin 6 → ZMod 2,
    t 2 + t 3 + t 5 = 0 →
    (unipotentProduct t * terminalZ).val (Atlas.SplitOctonion.basisVector 3) 0 =
      (terminalZ * unipotentProduct t).val (Atlas.SplitOctonion.basisVector 3) 0 →
    (unipotentProduct t * terminalZ).val (Atlas.SplitOctonion.basisVector 0) 1 =
      (terminalZ * unipotentProduct t).val (Atlas.SplitOctonion.basisVector 0) 1 →
    (unipotentProduct t * terminalZ).val (Atlas.SplitOctonion.basisVector 0) 0 =
      (terminalZ * unipotentProduct t).val (Atlas.SplitOctonion.basisVector 0) 0 →
    t = 0 ∨ t = ![0,1,1,1,1,0] := by
  decide +kernel


def smallFixer : Subgroup DerivedModel :=
  (derivedSylow : Subgroup DerivedModel) ⊓
    (Subgroup.centralizer {terminalZ}).comap DerivedModel.subtype

theorem path_fixer_le : pathStabilizer family path ≤ smallFixer := by
  have h := alternatingFive_fixer_le family true a b a_mem b_mem
  rw [family_inf] at h
  intro g hg
  have hh := h hg
  refine ⟨hh.1,Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
  have hm : longWord⁻¹ * g.val * longWord ∈ firstParabolic := by
    exact derivedSylow_le_first hh.2
  have he := firstParabolic_centralizes_z _ hm
  change g.val * (longWord * z * longWord⁻¹) = (longWord * z * longWord⁻¹) * g.val
  calc
    _ = longWord * (longWord⁻¹ * g.val * longWord) * z * longWord⁻¹ := by group
    _ = longWord * z * (longWord⁻¹ * g.val * longWord) * longWord⁻¹ := by rw [mul_assoc longWord,he]; group
    _ = _ := by group

private theorem smallFixer_coordinates (g : smallFixer) :
    ∃ t : Fin 6 → ZMod 2, (t = 0 ∨ t = ![0,1,1,1,1,0]) ∧ unipotentProduct t = g.val.val := by
  have hu : g.val.val ∈ unipotent := by
    have hh := g.prop.1
    rw [derivedSylow_eq] at hh
    exact hh
  rw [unipotent_eq_range] at hu
  obtain ⟨t,ht⟩ := hu
  refine ⟨t,?_,ht⟩
  have hd := (derived_parameters t).mp (ht ▸ g.val.prop)
  have hc : unipotentProduct t * terminalZ = terminalZ * unipotentProduct t := by
    rw [ht]
    exact Subgroup.mem_centralizer_singleton_iff.mp g.prop.2
  exact surviving_parameters t hd
    (congrArg (fun g : Model (ZMod 2) => g.val (Atlas.SplitOctonion.basisVector 3) 0) hc)
    (congrArg (fun g : Model (ZMod 2) => g.val (Atlas.SplitOctonion.basisVector 0) 1) hc)
    (congrArg (fun g : Model (ZMod 2) => g.val (Atlas.SplitOctonion.basisVector 0) 0) hc)

theorem card_smallFixer : Nat.card smallFixer ≤ 2 := by
  classical
  let T := {t : Fin 6 → ZMod 2 // t = 0 ∨ t = ![0,1,1,1,1,0]}
  let f : smallFixer → T := fun g =>
    ⟨(smallFixer_coordinates g).choose,(smallFixer_coordinates g).choose_spec.1⟩
  have hf : Function.Injective f := by
    intro g h he
    apply Subtype.ext
    apply Subtype.ext
    have ht := congrArg Subtype.val he
    exact (smallFixer_coordinates g).choose_spec.2.symm.trans
      ((congrArg unipotentProduct ht).trans (smallFixer_coordinates h).choose_spec.2)
  have hc : Nat.card T = 2 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  have hh := Nat.card_le_card_of_injective f hf
  rwa [hc] at hh

theorem path_fixer_card_le : Nat.card (pathStabilizer family path) ≤ 2 :=
  (Nat.card_le_card_of_injective (Subgroup.inclusion path_fixer_le)
    (Subgroup.inclusion_injective _)).trans card_smallFixer

theorem card_family (i : Bool) : Nat.card (family i) = 96 := by
  cases i
  · exact card_derivedFirst
  · exact card_derivedSecond

theorem family_indices (i : Bool) : ((family (!i)).subgroupOf (family i)).index = 3 := by
  have he : (family (!i)).subgroupOf (family i) =
      (derivedSylow : Subgroup DerivedModel).subgroupOf (family i) := by
    rw [← family_inf i,Subgroup.inf_subgroupOf_left]
  rw [he]
  cases i
  · exact derivedSylow_index_in_first
  · exact derivedSylow_index_in_second

theorem card_five_paths (i : Bool) :
    Nat.card {p : BasedWalk (graph family) 5 (base family i) // p.Nonbacktracking} = 48 := by
  have hc := card_neighbors_of_indices family (fun _ => 3) family_indices
  have (v : Vertex family) : Finite ((graph family).neighborSet v) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; decide)
  have hf : ∀ {v w : Vertex family}, (graph family).Adj v w → w.type = !v.type := by
    intro v w h
    have hn := h.1
    cases hv : v.type <;> cases hw : w.type <;> simp_all
  have hh := BasedWalk.card_nonbacktracking_succ (graph family)
    (fun v : Vertex family => v.type) (fun _ => 3) hf hc 4 (base family i)
  rw [hh]
  cases i <;> decide

theorem exists_path_fixer_card_le (i : Bool) :
    ∃ p : BasedWalk (graph family) 5 (base family i), p.Nonbacktracking ∧
      Nat.card (pathStabilizer family p) ≤ 2 := by
  cases i with
  | true => exact ⟨path,path_nb,path_fixer_card_le⟩
  | false =>
    let p := path
    have ht : p.endpoint.type = false := rfl
    let r := Theory.GroupAction.CubicTree.reverse p
    have hr : r.Nonbacktracking := Theory.GroupAction.CubicTree.nonbacktracking_reverse p path_nb
    obtain ⟨q,hq,g,hg⟩ := exists_base_path_translate family ht r hr
    refine ⟨q,hq,?_⟩
    have he : pathStabilizer family r = pathStabilizer family p := by
      ext x
      change (∀ w ∈ r.vertices, x • w = w) ↔ (∀ w ∈ p.vertices, x • w = w)
      simp only [r,Theory.GroupAction.CubicTree.vertices_reverse,List.mem_reverse]
    have hm := pathStabilizer_map_conj_of_vertices family q r g hg
    have hc : Nat.card (pathStabilizer family q) = Nat.card (pathStabilizer family p) := by
      rw [← he,← hm,Subgroup.card_map_of_injective (MulAut.conj g).injective]
    rw [hc]
    exact path_fixer_card_le

theorem rootPathTransitive_five (i : Bool) :
    RootPathTransitive (graph family) DerivedModel (base family i) 5 := by
  obtain ⟨p,hp,hc⟩ := exists_path_fixer_card_le i
  have : Finite {p : BasedWalk (graph family) 5 (base family i) // p.Nonbacktracking} :=
    Nat.finite_of_card_ne_zero (by rw [card_five_paths]; decide)
  apply rootPathTransitive_of_pathStabilizer_card_le family p hp (by decide : 0 < 2) hc
  rw [stabilizer,Subgroup.CosetGeometry.stabilizer_base,card_family,card_five_paths]



def endWord : DerivedModel := b*a*b*a*b

private theorem fix_base {g : DerivedModel} {i : Bool} (hg : g ∈ family i) :
    g • base family i = base family i := by
  change g ∈ stabilizer family (base family i)
  simpa only [stabilizer,base,Subgroup.CosetGeometry.stabilizer_base] using hg

private theorem translate_ne {g : DerivedModel} {i : Bool} (hg : g ∉ family i) :
    g • base family i ≠ base family i := fun he => hg (by
      have hh : g ∈ stabilizer family (base family i) := he
      simpa only [stabilizer,base,Subgroup.CosetGeometry.stabilizer_base] using hh)

private theorem end_edge : (graph family).Adj path.endpoint (endWord • base family true) := by
  have hh : (graph family).Adj (base family false) (base family true) :=
    ⟨by decide,Subgroup.CosetGeometry.incident_base family false true⟩
  have h := (Subgroup.CosetGeometry.translationGraphIso family endWord).toHom.map_adj hh
  change (graph family).Adj (endWord • base family false) _ at h
  change (graph family).Adj ((b*a*b*a) • base family false) (endWord • base family true)
  have hb : b • base family false = base family false := fix_base b_mem
  have he : endWord • base family false = (b*a*b*a) • base family false := by
    change ((b*a*b*a)*b) • base family false = _
    rw [mul_smul,hb]
  rw [he] at h
  exact h

def sixPath : BasedWalk (graph family) 6 (base family true) := path.snoc (z := endWord • base family true) (by exact end_edge)

theorem sixPath_vertices : sixPath.vertices =
    [base family true,base family false,b • base family true,
      (b*a) • base family false,(b*a*b) • base family true,
      (b*a*b*a) • base family false,endWord • base family true] := by
  rw [sixPath,BasedWalk.vertices_snoc]
  rfl

theorem sixPath_nb : sixPath.Nonbacktracking := by
  rw [sixPath,BasedWalk.nonbacktracking_snoc_iff]
  refine ⟨path_nb,?_⟩
  change endWord • base family true ≠ (b*a*b) • base family true
  have he : (b*a*b) • base family true = (b*a*b*a) • base family true := by
    rw [mul_smul (b*a*b) a,fix_base a_mem]
  rw [he]
  intro hh
  apply translate_ne b_not_mem
  have hh' := congrArg (fun v : Vertex family => (b*a*b*a)⁻¹ • v) hh
  change (b*a*b*a)⁻¹ • (((b*a*b*a)*b) • base family true) =
    (b*a*b*a)⁻¹ • ((b*a*b*a) • base family true) at hh'
  rwa [mul_smul (b*a*b*a) b,inv_smul_smul,inv_smul_smul] at hh'

def coord (t : Fin 6 → ZMod 2) (ht : t 2 + t 3 + t 5 = 0) : DerivedModel :=
  ⟨unipotentProduct t,by exact (derived_parameters t).mpr ht⟩

private theorem coord_mem (t : Fin 6 → ZMod 2) (ht : t 2+t 3+t 5=0) (i : Bool) :
    coord t ht ∈ family i := by
  have hh : coord t ht ∈ (derivedSylow : Subgroup DerivedModel) := by
    rw [derivedSylow_eq]
    exact unipotentProduct_mem t
  cases i
  · exact derivedSylow_le_first hh
  · exact derivedSylow_le_second hh

def mover : DerivedModel := coord ![0,1,1,1,1,0] (by decide)

private theorem mover_conjugates :
    b⁻¹ * mover * b = coord ![1,1,0,0,0,0] (by decide) ∧
    (b*a)⁻¹ * mover * (b*a) = coord ![1,0,0,0,0,0] (by decide) ∧
    (b*a*b)⁻¹ * mover * (b*a*b) = coord ![1,0,0,0,0,0] (by decide) ∧
    (b*a*b*a)⁻¹ * mover * (b*a*b*a) = coord ![0,1,0,0,0,0] (by decide) ∧
    endWord⁻¹ * mover * endWord = coord ![0,0,0,0,1,0] (by decide) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  all_goals
    apply Subtype.ext
    apply Subtype.ext
    apply LinearEquiv.toLinearMap_injective
    apply (Pi.basisFun (ZMod 2) (Fin 8)).ext
    intro j
    funext i
    simp only [Pi.basisFun_apply]
    revert j i
    decide +kernel

private theorem fixes_translate {g w : DerivedModel} {i : Bool}
    (hg : w⁻¹*g*w ∈ family i) : g • (w • base family i) = w • base family i := by
  have hh := fix_base hg
  apply (MulAction.toPerm w⁻¹).injective
  simpa only [MulAction.toPerm_apply,mul_smul,inv_smul_smul] using hh

theorem mover_fixes : mover ∈ pathStabilizer family sixPath := by
  rcases mover_conjugates with ⟨h1,h2,h3,h4,h5⟩
  intro v hv
  rw [sixPath_vertices] at hv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact fix_base (coord_mem _ _ true)
  · exact fix_base (coord_mem _ _ false)
  · exact fixes_translate (h1 ▸ coord_mem _ _ true)
  · exact fixes_translate (h2 ▸ coord_mem _ _ false)
  · exact fixes_translate (h3 ▸ coord_mem _ _ true)
  · exact fixes_translate (h4 ▸ coord_mem _ _ false)
  · exact fixes_translate (h5 ▸ coord_mem _ _ true)

theorem mover_ne_one : mover ≠ 1 := by
  intro he
  have hh := congrArg (fun g : DerivedModel => g.val.val (Atlas.SplitOctonion.basisVector 5) 0) he
  have hv : mover.val.val (Atlas.SplitOctonion.basisVector 5) 0 = 1 := by decide +kernel
  have hz : (1 : DerivedModel).val.val (Atlas.SplitOctonion.basisVector 5) 0 = 0 := by decide +kernel
  rw [hv,hz] at hh
  exact one_ne_zero hh

theorem card_six_paths :
    Nat.card {p : BasedWalk (graph family) 6 (base family true) // p.Nonbacktracking} = 96 := by
  have hc := card_neighbors_of_indices family (fun _ => 3) family_indices
  have (v : Vertex family) : Finite ((graph family).neighborSet v) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; decide)
  have hf : ∀ {v w : Vertex family}, (graph family).Adj v w → w.type = !v.type := by
    intro v w h
    have hn := h.1
    cases hv : v.type <;> cases hw : w.type <;> simp_all
  have hh := BasedWalk.card_nonbacktracking_succ (graph family)
    (fun v : Vertex family => v.type) (fun _ => 3) hf hc 5 (base family true)
  rw [hh]
  decide

theorem not_rootPathTransitive_six :
    ¬ RootPathTransitive (graph family) DerivedModel (base family true) 6 := by
  intro ht
  have hc := card_paths_mul_card_fixer family ht sixPath sixPath_nb
  rw [card_six_paths,stabilizer,Subgroup.CosetGeometry.stabilizer_base,card_family] at hc
  have hc1 : Nat.card (pathStabilizer family sixPath) = 1 := by omega
  have hb : pathStabilizer family sixPath = ⊥ := Subgroup.card_eq_one.mp hc1
  exact mover_ne_one (by simpa only [hb,Subgroup.mem_bot] using mover_fixes)

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.BinaryPaths
