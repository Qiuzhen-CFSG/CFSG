module
public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon.ShortGirth
public import Theory.GroupAction.RankTwoCosetCover.PathTransport
public import Theory.GroupAction.DihedralPolygon.CycleAutomorphisms
public import Theory.GroupTheory.CoprimeSubgroupLift

/-!
# Dihedral lifts of a twelve-cycle

In a graph of girth at least twelve, an automorphism matching seven
successive edges of a twelve-cycle matches the complementary five-edge
path as well. Rooted seven-path transitivity therefore realizes the two
vertex reflections of the cycle. Pairing these ambient actions with their
polygon permutations gives a surjection onto the dihedral group of order
twelve. If the pointwise cycle fixer lies in a subgroup of order coprime
to twelve, Schur–Zassenhaus splits this surjection. Its two reflections
are actual ambient involutions whose product has sixth power one.

Source: Aschbacher–Smith F.4.15–16, printed pp.281–282
(`refs/quasithin.pdf`). The coprime kernel is explicit; the binary triality
application supplies it from the seven-path stabilizer of order seven.
-/

@[expose] public noncomputable section
open SimpleGraph SimpleGraph.PathTransitivePolygon Fin.NatCast
namespace GroupAction.HexagonReflections
variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

def arc (f : cycleGraph 12 →g Γ) (a : Fin 12) : (n : ℕ) → BasedWalk Γ n (f a)
  | 0 => PUnit.unit
  | n+1 => ⟨⟨f (a+1), f.map_rel' (by rw [cycleGraph_adj]; right; abel)⟩, arc f (a+1) n⟩

@[simp] theorem arc_endpoint (f : cycleGraph 12 →g Γ) (a : Fin 12) (n : ℕ) :
    (arc f a n).endpoint = f (a + (↑n : Fin 12)) := by
  induction n generalizing a with
  | zero => simp [BasedWalk.endpoint]
  | succ n ih =>
    change (arc f (a+1) n).endpoint = _
    rw [ih]
    congr 1
    push_cast
    abel

@[simp] theorem arc_vertices (f : cycleGraph 12 →g Γ) (a : Fin 12) (n : ℕ) :
    (arc f a n).vertices = List.ofFn (fun i : Fin (n+1) => f (a + (↑i.val : Fin 12))) := by
  induction n generalizing a with
  | zero => simp [BasedWalk.vertices]
  | succ n ih =>
    change f a :: (arc f (a+1) n).vertices = _
    rw [ih]
    conv_rhs => rw [List.ofFn_succ]
    apply congrArg₂ List.cons
    · simp
    · apply congrArg List.ofFn
      funext i
      congr 1
      simp only [Fin.val_succ,Nat.cast_add,Nat.cast_one]
      abel

theorem arc_nonbacktracking (f : cycleGraph 12 →g Γ) (hf : Function.Injective f)
    (a : Fin 12) (n : ℕ) : (arc f a n).Nonbacktracking := by
  induction n generalizing a with
  | zero => trivial
  | succ n ih =>
    cases n with
    | zero => trivial
    | succ n =>
      refine ⟨fun he => ?_, ih (a+1)⟩
      exact (show ∀ a : Fin 12, a+1+1 ≠ a by decide +kernel) a (hf he)

private theorem short_paths_eq
    (hg : ∀ v (p : Γ.Walk v v), p.IsCycle → 12 ≤ p.length)
    {v w : V} {p q : Γ.Walk v w} (hp : p.IsPath) (hq : q.IsPath)
    (hn : p.length + q.length < 12) : p=q := by
  by_contra h
  obtain ⟨u,_,_,r,hr,hl⟩ := hp.exists_isCycle_length_le_add_of_ne hq h
  have := hg u r hr
  omega

/-- Agreement on seven successive edges determines the whole twelve-cycle. -/
theorem extend_agreement
    (act : GraphAction Γ G)
    (hg : ∀ v (p : Γ.Walk v v), p.IsCycle → 12 ≤ p.length)
    (f k : cycleGraph 12 →g Γ) (hf : Function.Injective f) (hk : Function.Injective k)
    (a : Fin 12) (g : G)
    (h : ∀ i : Fin 8, g • f (a+(↑i.val : Fin 12)) = k (a+(↑i.val : Fin 12))) :
    ∀ i, g • f i = k i := by
  let φ : Γ →g Γ := ⟨(g • ·),act.map_adj g⟩
  let p := (arc f (a+7) 5).map φ
  let q := arc k (a+7) 5
  have hs : g • f (a+7) = k (a+7) := h 7
  have he : p.endpoint = q.endpoint := by
    simp only [p,q,BasedWalk.endpoint_map,arc_endpoint]
    change g • f (a+7+5)=k (a+7+5)
    have hc : (a+7+(5 : Fin 12))=a := by have h : (7+5 : Fin 12)=0 := rfl; simp only [add_assoc,h,add_zero]
    rw [hc]
    simpa only [Fin.val_zero,Nat.cast_zero,add_zero] using h 0
  have hp := isPath_of_nonbacktracking_of_cycle_bound (N := 11)
    (fun v r hr => by have := hg v r hr; omega) p
    ((act.nonbacktracking_map_iff g _).mpr (arc_nonbacktracking f hf _ _)) (by decide)
  have hq := isPath_of_nonbacktracking_of_cycle_bound (N := 11)
    (fun v r hr => by have := hg v r hr; omega) q (arc_nonbacktracking k hk _ _) (by decide)
  have hw : p.toWalk.copy hs he = q.toWalk := short_paths_eq hg
    ((Walk.isPath_copy _ _ _).mpr hp) hq (by simp only [Walk.length_copy,BasedWalk.length_toWalk]; decide)
  have hl := congrArg Walk.support hw
  simp only [Walk.support_copy,BasedWalk.support_toWalk,p,q,BasedWalk.vertices_map,
    arc_vertices,List.map_ofFn] at hl
  have ht : ∀ i : Fin 6, g • f (a+7+(↑i.val : Fin 12)) = k (a+7+(↑i.val : Fin 12)) := by
    have hh := List.ofFn_injective hl
    intro i
    exact congrFun hh i
  intro i
  have hh : ∃ j : Fin 12, i=a+j := ⟨i-a,by abel⟩
  obtain ⟨j,rfl⟩ := hh
  fin_cases j
  all_goals first
    | exact h 0 | exact h 1 | exact h 2 | exact h 3
    | exact h 4 | exact h 5 | exact h 6 | exact h 7
    | simpa [add_assoc] using ht 1
    | simpa [add_assoc] using ht 2
    | simpa [add_assoc] using ht 3
    | simpa [add_assoc] using ht 4

/-- Rooted seven-path transitivity lifts every cycle automorphism fixing a vertex. -/
theorem lift_fixed_cycle_automorphism
    (act : GraphAction Γ G)
    (hg : ∀ v (p : Γ.Walk v v), p.IsCycle → 12 ≤ p.length)
    (htrans : ∀ v, RootPathTransitive Γ G v 7)
    (f : cycleGraph 12 →g Γ) (hf : Function.Injective f)
    (r : cycleGraph 12 ≃g cycleGraph 12) (a : Fin 12) (ha : r a=a) :
    ∃ g : G, ∀ i, g • f i=f (r i) := by
  let k := f.comp r.toHom
  let p := arc f a 7
  have hbase : k a=f a := congrArg f ha
  let q := BasedWalk.rebase hbase (arc k a 7)
  obtain ⟨g,_,hg'⟩ := htrans (f a) p q (arc_nonbacktracking f hf _ _)
    ((BasedWalk.nonbacktracking_rebase _ _).mpr
      (arc_nonbacktracking k (hf.comp r.injective) _ _))
  refine ⟨g,extend_agreement act hg f k hf (hf.comp r.injective) a g ?_⟩
  simp only [p,q,BasedWalk.vertices_rebase,arc_vertices,List.map_ofFn] at hg'
  have he := List.ofFn_injective hg'
  intro i
  exact congrFun he i

end GroupAction.HexagonReflections

namespace GroupAction.HexagonReflections
open Subgroup
open GroupAction.DihedralPolygon.CycleAutomorphisms
variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

/-- The standard action of the type-preserving dihedral group on twelve vertices. -/
def polygonAction : DihedralGroup 6 →* Equiv.Perm (Fin 12) :=
  (graphAut (cycleGraph 12)).subtype.comp
    ((parityPreserving 6).subtype.comp (dihedralHom (by decide)))

/-- Simultaneous ambient and polygon actions agreeing on the actual labelled cycle. -/
def liftGroup (f : Fin 12 → V) : Subgroup (G × DihedralGroup 6) where
  carrier := {p | ∀ i, p.1 • f i = f (polygonAction p.2 i)}
  one_mem' := by intro i; simp
  mul_mem' := by
    intro x y hx hy i
    change (x.1*y.1) • f i = f (polygonAction (x.2*y.2) i)
    rw [mul_smul,hy,hx,map_mul,Equiv.Perm.mul_apply]
  inv_mem' := by
    intro x hx i
    change x.1⁻¹ • f i=f (polygonAction x.2⁻¹ i)
    have h := hx (polygonAction x.2⁻¹ i)
    rw [←Equiv.Perm.mul_apply,←map_mul,mul_inv_cancel,map_one] at h
    have hh := congrArg (fun v => x.1⁻¹ • v) h
    simpa only [inv_smul_smul,Equiv.Perm.one_apply] using hh.symm

def projection (f : Fin 12 → V) : liftGroup (G := G) f →* DihedralGroup 6 :=
  (MonoidHom.snd G (DihedralGroup 6)).comp (liftGroup f).subtype

private theorem projection_surjective (f : Fin 12 → V)
    (hs : ∃ g : G, ∀ i, g • f i=f (polygonAction (.sr 0) i))
    (ht : ∃ g : G, ∀ i, g • f i=f (polygonAction (.sr (-1)) i)) :
    Function.Surjective (projection (G := G) f) := by
  obtain ⟨s,hs⟩ := hs
  obtain ⟨t,ht⟩ := ht
  have h0 : DihedralGroup.sr 0 ∈ (projection (G := G) f).range := ⟨⟨(s,.sr 0),hs⟩,rfl⟩
  have h1 : DihedralGroup.sr (-1) ∈ (projection (G := G) f).range := ⟨⟨(t,.sr (-1)),ht⟩,rfl⟩
  have hr : DihedralGroup.r 1 ∈ (projection (G := G) f).range := by
    simpa only [DihedralGroup.sr_mul_sr,zero_sub,neg_neg] using
      (projection (G := G) f).range.mul_mem h1 h0
  have hrot (a : ZMod 6) : DihedralGroup.r a ∈ (projection (G := G) f).range := by
    have h := (projection (G := G) f).range.pow_mem hr a.val
    simpa only [DihedralGroup.r_one_pow,ZMod.natCast_zmod_val] using h
  intro w
  cases w with
  | r a => exact hrot a
  | sr a =>
    change DihedralGroup.sr a ∈ (projection (G := G) f).range
    simpa only [DihedralGroup.sr_mul_r,zero_add] using
      (projection (G := G) f).range.mul_mem h0 (hrot a)

/-- A coprime pointwise cycle kernel splits; the original cycle receives an
actual dihedral action inside the ambient group. -/
theorem exists_dihedral_lift (f : Fin 12 → V)
    (hs : ∃ g : G, ∀ i, g • f i=f (polygonAction (.sr 0) i))
    (ht : ∃ g : G, ∀ i, g • f i=f (polygonAction (.sr (-1)) i))
    (Q : Subgroup G) (hQ : ∀ g : G, (∀ i, g • f i=f i) → g∈Q)
    (hcop : (Nat.card Q).Coprime 12) :
    ∃ d : DihedralGroup 6 →* G, ∀ w i, d w • f i=f (polygonAction w i) := by
  let π := projection (G := G) f
  let j : π.ker →* Q := {
    toFun := fun x => ⟨x.val.val.1,by
      apply hQ
      intro i
      have hh := x.val.property i
      have hx : x.val.val.2=1 := x.property
      simpa only [hx,map_one,Equiv.Perm.one_apply] using hh⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Subtype.val h
    · exact x.property.trans y.property.symm
  have hcard : Nat.card π.ker ∣ Nat.card Q := Subgroup.card_dvd_of_injective j hj
  have hker : (Nat.card π.ker).Coprime (Nat.card (⊤ : Subgroup (DihedralGroup 6))) := by
    rw [Subgroup.card_top,Nat.card_eq_fintype_card (α := DihedralGroup 6),DihedralGroup.card]
    exact hcop.of_dvd_left hcard
  obtain ⟨l,hl⟩ := π.exists_subgroup_section_of_coprime_kernel
    (projection_surjective f hs ht) ⊤ hker
  let u : DihedralGroup 6 →* liftGroup (G := G) f :=
    l.comp (Subgroup.topEquiv.symm.toMonoidHom)
  let d := (MonoidHom.fst G (DihedralGroup 6)).comp ((liftGroup f).subtype.comp u)
  refine ⟨d,?_⟩
  intro w i
  have hw : π (u w)=w := DFunLike.congr_fun hl (Subgroup.topEquiv.symm w)
  exact (u w).property i |>.trans (congrArg (fun z => f (polygonAction z i)) hw)

/-- Seven-path transitivity and a coprime pointwise fixer supply true endpoint
involutions with the sixth-power relation on this same cycle. -/
theorem exists_reflections
    (act : GraphAction Γ G)
    (hg : ∀ v (p : Γ.Walk v v), p.IsCycle → 12 ≤ p.length)
    (htrans : ∀ v, RootPathTransitive Γ G v 7)
    (f : cycleGraph 12 →g Γ) (hf : Function.Injective f)
    (Q : Subgroup G) (hQ : ∀ g : G, (∀ i, g • f i=f i) → g∈Q)
    (hcop : (Nat.card Q).Coprime 12) :
    ∃ s t : G, s^2=1 ∧ t^2=1 ∧ (s*t)^6=1 ∧
      s • f 0=f 0 ∧ s • f 1≠f 1 ∧ t • f 1=f 1 ∧ t • f 0≠f 0 := by
  have hlift (a : ZMod 6) (i : Fin 12) (hi : polygonAction (.sr a) i=i) :
      ∃ g : G, ∀ j, g • f j=f (polygonAction (.sr a) j) :=
    lift_fixed_cycle_automorphism act hg htrans f hf
      (graphAutEquivIso _ (dihedralHom (by decide) (.sr a)).val) i hi
  obtain ⟨d,hd⟩ := exists_dihedral_lift (G := G) f
    (hlift 0 0 rfl) (hlift (-1) 1 (by decide +kernel)) Q hQ hcop
  refine ⟨d (.sr 0),d (.sr (-1)),?_,?_,?_,?_,?_,?_,?_⟩
  · rw [←map_pow]; simp only [DihedralGroup.sr_mul_sr,sub_self,DihedralGroup.r_zero,pow_two,map_one]
  · rw [←map_pow]; simp only [DihedralGroup.sr_mul_sr,sub_self,DihedralGroup.r_zero,pow_two,map_one]
  · rw [←map_mul,←map_pow]
    have h : ((DihedralGroup.sr 0 : DihedralGroup 6)*.sr (-1))^6=1 := by decide +kernel
    rw [h,map_one]
  · exact hd (.sr 0) 0
  · rw [hd]
    exact hf.ne (by decide : polygonAction (.sr 0) 1≠1)
  · simpa only [show polygonAction (.sr (-1)) 1=1 from by decide +kernel] using hd (.sr (-1)) 1
  · rw [hd]
    exact hf.ne (by decide : polygonAction (.sr (-1)) 0≠0)

end GroupAction.HexagonReflections
