module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Six

/-!
# Edge and fixed-core transport through regular turns

Uniqueness of the two-edge path identifies the transported middle vertex.
Equal incident edge commutators make a turn preserve the subgroup and carry
its fixed-core containment backward. The next turn can be taken in the
residual, which fixes that subgroup pointwise and transports its edge formula.

Source: Meierfrankenfeld--Stellmacher (1993), the equivalence of ordered
pairs in (4.4.4), printed p.894. These are geometric transport lemmas;
the natural-module proof of equality of the incident edges remains separate.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Iteration
variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : Geometry R}

include geometry

private theorem middle_unique {c d t s : Vertex R}
    (hcd : (cosetGraph R).dist c d = 2)
    (hct : Adjacent R c t) (htd : Adjacent R t d)
    (hcs : Adjacent R c s) (hsd : Adjacent R s d) : t = s := by
  let q : (cosetGraph R).Walk c d := .cons ((cosetGraph_adj R _ _).mpr hct)
    (.cons ((cosetGraph_adj R _ _).mpr htd) .nil)
  let r : (cosetGraph R).Walk c d := .cons ((cosetGraph_adj R _ _).mpr hcs)
    (.cons ((cosetGraph_adj R _ _).mpr hsd) .nil)
  have hq : q.IsPath := q.isPath_of_length_eq_dist (by simpa only [q,
    SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] using hcd.symm)
  have hr : r.IsPath := r.isPath_of_length_eq_dist (by simpa only [r,
    SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] using hcd.symm)
  have he := congrArg Subtype.val
    ((geometry.tree.isAcyclic.subsingleton_path c d).elim ⟨q, hq⟩ ⟨r, hr⟩)
  exact congrArg (fun w => w.getVert 1) he

theorem turn_middle {a c d s t : Vertex R}
    (hca : (cosetGraph R).dist c a = 2)
    (hct : Adjacent R c t) (htd : Adjacent R t d)
    (hcs : Adjacent R c s) (hsa : Adjacent R s a)
    {g : FreeAmalgam R} (hg : g ∈ stabilizer R c)
    (hturn : Stellmacher.PushingUp.AmalgamGraph.act R g d = a) :
    Stellmacher.PushingUp.AmalgamGraph.act R g t = s := by
  have hgc : Stellmacher.PushingUp.AmalgamGraph.act R g c = c := hg
  apply middle_unique (geometry := geometry) hca _ _ hcs hsa
  · simpa only [hgc] using (adjacent_act_iff R g c t).mpr hct
  · simpa only [hturn] using (adjacent_act_iff R g t d).mpr htd

omit geometry in
theorem map_eq_self_of_le_fixed {c : Vertex R} {K : Subgroup (FreeAmalgam R)}
    (hK : K ≤ fixedCore R c) {l : FreeAmalgam R} (hl : l ∈ Ltilde R c) :
    K.map (MulAut.conj l⁻¹).toMonoidHom = K := by
  have hfix (x : FreeAmalgam R) (hx : x ∈ K) : (MulAut.conj l⁻¹) x = x := by
    have hh := (hK hx).2 l⁻¹ ((Ltilde R c).inv_mem hl)
    change l⁻¹ * x * (l⁻¹)⁻¹ = x
    rw [hh, mul_inv_cancel_right]
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    change (MulAut.conj l⁻¹) x ∈ K
    rw [hfix x hx]
    exact hx
  · intro x hx
    exact ⟨x, hx, hfix x hx⟩

/-- Equal incident edges make the turn preserve K, carrying its fixed-core
containment from one endpoint of the two-step turn to the other. -/
theorem transport_fixed_of_equal_edges
    {a c d s t : Vertex R}
    (hca : (cosetGraph R).dist c a = 2)
    (hct : Adjacent R c t) (htd : Adjacent R t d)
    (hcs : Adjacent R c s) (hsa : Adjacent R s a)
    {g : FreeAmalgam R} (hg : g ∈ stabilizer R c)
    (hturn : Stellmacher.PushingUp.AmalgamGraph.act R g d = a)
    {K : Subgroup (FreeAmalgam R)}
    (hforward : K = edgeCommutator R c t) (hbackward : K = edgeCommutator R c s)
    (hfixed : K ≤ fixedCore R d) : K ≤ fixedCore R a := by
  have hmiddle := turn_middle (geometry := geometry) hca hct htd hcs hsa hg hturn
  have hgc : Stellmacher.PushingUp.AmalgamGraph.act R g c = c := hg
  have hmap : K.map (MulAut.conj g⁻¹).toMonoidHom = K := by
    calc
      K.map (MulAut.conj g⁻¹).toMonoidHom =
          (edgeCommutator R c t).map (MulAut.conj g⁻¹).toMonoidHom := congrArg _ hforward
      _ = edgeCommutator R c s := by rw [← edgeCommutator_act, hgc, hmiddle]
      _ = K := hbackward.symm
  have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hfixed
  rwa [hmap, ← Escape.EdgeTransfer.fixedCore_act, hturn] at hh

/-- A residual turn fixing K pointwise carries its edge description across
the next two edges. -/
theorem transport_edge_of_fixed [Finite M] (source : LocalSource L R)
    {a c d s t : Vertex R} (hc : color R c = false)
    (hca : (cosetGraph R).dist c a = 2)
    (hct : Adjacent R c t) (htd : Adjacent R t d)
    (hcs : Adjacent R c s) (hsa : Adjacent R s a)
    {g : FreeAmalgam R} (hg : g ∈ stabilizer R c)
    (hturn : Stellmacher.PushingUp.AmalgamGraph.act R g d = a)
    {K : Subgroup (FreeAmalgam R)}
    (hedge : K = edgeCommutator R d t) (hfixed : K ≤ fixedCore R c) :
    K = edgeCommutator R a s := by
  obtain ⟨l, hl, hturn⟩ := exists_residual_turn source hc hca hg hturn
  have hlc : l ∈ stabilizer R c := Ltilde_le_stabilizer c hl
  have hmiddle := turn_middle (geometry := geometry) hca hct htd hcs hsa hlc hturn
  calc
    K = K.map (MulAut.conj l⁻¹).toMonoidHom := (map_eq_self_of_le_fixed hfixed hl).symm
    _ = edgeCommutator R a s := by rw [hedge, ← edgeCommutator_act, hturn, hmiddle]

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Iteration
