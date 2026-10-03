module

public import Mathlib.GroupTheory.PushoutI
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Stellmacher.SectionsOneToFourDefs

/-!
# The faithful locally finite amalgam graph for pushing up

This module constructs the free amalgam `M *_S Hol(S)` and its right-coset
graph used in Stellmacher's 1986 pushing-up proof.  It establishes the exact
factor intersection and all of the source's elementary graph facts:
connectedness, bipartiteness, edge transitivity, finite neighborhoods, local
transitivity, the vertex and edge stabilizers, and faithfulness under (P).

The ambient amalgam and its vertex type remain generally infinite.  Only the
two vertex factors and individual neighborhoods are proved finite, matching
the locally finite source argument and avoiding a finite-completion
substitution.

The exact intersection follows from the normal form for `Monoid.PushoutI`.
Connectedness is proved by induction on its factor generators and products;
explicit factor parametrizations give finite neighborhoods and local
transitivity.  Finally, the action kernel lies in the adjacent-factor
intersection, and invariance under both factors pulls it back to a
characteristic subgroup of `S` normal in `M`, which (P) excludes.  These are
the specialized `B = S`, `A = Aut(S)` forms of Stellmacher, *Pushing up*,
Arch. Math. 46 (1986), (1.1)--(1.2).
-/

@[expose] public section

namespace Stellmacher.PushingUp.AmalgamGraph

universe u

open scoped Pointwise

inductive Side
  | m
  | h
  deriving DecidableEq

variable {M : Type u} [Group M] (S : Subgroup M)

abbrev Holomorph : Type u :=
  S ⋊[MonoidHom.id (MulAut S)] MulAut S

private noncomputable instance finiteMulAut [Finite M] : Finite (MulAut S) := by
  apply Finite.of_injective (fun a : MulAut S => (a : S → S))
  intro a b hab
  apply DFunLike.ext a b
  intro s
  exact congrFun hab s

private noncomputable instance finiteHolomorph [Finite M] : Finite (Holomorph S) := by
  apply Finite.of_injective (fun h : Holomorph S => (h.left, h.right))
  intro a b hab
  exact SemidirectProduct.ext (congrArg Prod.fst hab) (congrArg Prod.snd hab)

def factor : Side → Type u
  | .m => M
  | .h => Holomorph S

instance factorGroup (i : Side) : Group (factor S i) := by
  cases i <;> simp only [factor] <;> infer_instance

def diagram : (i : Side) → S →* factor S i
  | .m => S.subtype
  | .h => SemidirectProduct.inl

theorem diagram_injective (i : Side) : Function.Injective (diagram S i) := by
  cases i with
  | m => exact S.subtype_injective
  | h => exact SemidirectProduct.inl_injective

abbrev FreeAmalgam : Type u := Monoid.PushoutI (diagram S)

def embedM : M →* FreeAmalgam S :=
  Monoid.PushoutI.of (φ := diagram S) Side.m

def embedH : Holomorph S →* FreeAmalgam S :=
  Monoid.PushoutI.of (φ := diagram S) Side.h

def embedS : S →* FreeAmalgam S :=
  Monoid.PushoutI.base (diagram S)

theorem embedM_injective : Function.Injective (embedM S) :=
  Monoid.PushoutI.of_injective (φ := diagram S) (diagram_injective S) Side.m

theorem embedH_injective : Function.Injective (embedH S) :=
  Monoid.PushoutI.of_injective (φ := diagram S) (diagram_injective S) Side.h

theorem embedS_injective : Function.Injective (embedS S) :=
  Monoid.PushoutI.base_injective (diagram_injective S)

theorem embedM_comp_subtype :
    (embedM S).comp S.subtype = embedS S :=
  Monoid.PushoutI.of_comp_eq_base (φ := diagram S) Side.m

theorem embedH_comp_inl :
    (embedH S).comp SemidirectProduct.inl = embedS S :=
  Monoid.PushoutI.of_comp_eq_base (φ := diagram S) Side.h

def Mbar : Subgroup (FreeAmalgam S) := (embedM S).range

def Hbar : Subgroup (FreeAmalgam S) := (embedH S).range

def Sbar : Subgroup (FreeAmalgam S) := (embedS S).range

theorem Mbar_inf_Hbar : Mbar S ⊓ Hbar S = Sbar S := by
  exact Monoid.PushoutI.inf_of_range_eq_base_range
    (φ := diagram S) (diagram_injective S) (by decide : Side.m ≠ Side.h)

def IsInvariantBy {G : Type*} [Group G] (N K : Subgroup G) : Prop :=
  ∀ k : G, k ∈ K → ∀ n : G, n ∈ N → k * n * k⁻¹ ∈ N

private theorem embedS_aut_conj (a : MulAut S) (s : S) :
    embedS S (a s) =
      embedH S (SemidirectProduct.inr a) * embedS S s *
        (embedH S (SemidirectProduct.inr a))⁻¹ := by
  have h := congrArg (embedH S) (SemidirectProduct.inl_aut a s)
  have hcomp (t : S) :
      embedH S (SemidirectProduct.inl t) = embedS S t :=
    DFunLike.congr_fun (embedH_comp_inl S) t
  simpa only [MonoidHom.id_apply, map_mul, map_inv, hcomp] using h

private theorem comap_embedS_characteristic
    (N : Subgroup (FreeAmalgam S))
    (hNH : IsInvariantBy N (Hbar S)) :
    (N.comap (embedS S)).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro a
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    change embedS S (a x) ∈ N
    rw [embedS_aut_conj]
    exact hNH _ ⟨SemidirectProduct.inr a, rfl⟩ _ hx
  · intro y hy
    refine ⟨a⁻¹ y, ?_, by simp⟩
    change embedS S (a⁻¹ y) ∈ N
    rw [embedS_aut_conj]
    exact hNH _ ⟨SemidirectProduct.inr a⁻¹, rfl⟩ _ hy

private theorem comap_embedM_normal
    (N : Subgroup (FreeAmalgam S))
    (hNM : IsInvariantBy N (Mbar S)) :
    (N.comap (embedM S)).Normal := by
  constructor
  intro n hn m
  change embedM S (m * n * m⁻¹) ∈ N
  simpa only [map_mul, map_inv] using
    hNM (embedM S m) ⟨m, rfl⟩ (embedM S n) hn

private theorem map_comap_embedS_subtype_eq_comap_embedM
    (N : Subgroup (FreeAmalgam S)) (hNS : N ≤ Sbar S) :
    (N.comap (embedS S)).map S.subtype = N.comap (embedM S) := by
  ext m
  constructor
  · rintro ⟨s, hs, rfl⟩
    change embedM S (s : M) ∈ N
    change embedS S s ∈ N at hs
    have heq : embedM S (s : M) = embedS S s :=
      DFunLike.congr_fun (embedM_comp_subtype S) s
    rwa [heq]
  · intro hm
    have hmS : embedM S m ∈ Sbar S := hNS hm
    rcases hmS with ⟨s, hs⟩
    have hms : m = (s : M) := by
      apply embedM_injective S
      calc
        embedM S m = embedS S s := hs.symm
        _ = embedM S (s : M) :=
          (DFunLike.congr_fun (embedM_comp_subtype S) s).symm
    subst m
    refine ⟨s, ?_, rfl⟩
    change embedS S s ∈ N
    rwa [← DFunLike.congr_fun (embedM_comp_subtype S) s]

theorem no_nontrivial_common_invariant
    [Finite M] (T : Sylow 2 M)
    (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (N : Subgroup (FreeAmalgam S))
    (hNS : N ≤ Sbar S)
    (hNM : IsInvariantBy N (Mbar S))
    (hNH : IsInvariantBy N (Hbar S)) :
    N = ⊥ := by
  subst S
  let K : Subgroup T := N.comap (embedS (T : Subgroup M))
  have hKchar : K.Characteristic :=
    comap_embedS_characteristic (T : Subgroup M) N hNH
  have hKMnormal : (N.comap (embedM (T : Subgroup M))).Normal :=
    comap_embedM_normal (T : Subgroup M) N hNM
  have hKmap : K.map (T : Subgroup M).subtype =
      N.comap (embedM (T : Subgroup M)) :=
    map_comap_embedS_subtype_eq_comap_embedM (T : Subgroup M) N hNS
  by_contra hN
  have hKne : K ≠ ⊥ := by
    intro hK
    apply hN
    apply le_bot_iff.mp
    intro n hn
    have hnS := hNS hn
    rcases hnS with ⟨s, rfl⟩
    have hsK : s ∈ K := hn
    rw [hK] at hsK
    simpa using congrArg (embedS (T : Subgroup M)) (show s = 1 by simpa using hsK)
  exact hP K hKchar hKne (hKmap ▸ hKMnormal)

/-! ## Right cosets and the bipartite incidence graph -/

abbrev RightCosets {G : Type*} [Group G] (K : Subgroup G) :=
  Quotient (QuotientGroup.rightRel K)

def rightCoset {G : Type*} [Group G] (K : Subgroup G) (g : G) :
    RightCosets K :=
  Quotient.mk (QuotientGroup.rightRel K) g

def rightCosetSet {G : Type*} [Group G] (K : Subgroup G) :
    RightCosets K → Set G :=
  Quotient.lift (fun g => MulOpposite.op g • (K : Set G)) (by
    intro a b hab
    exact (rightCoset_eq_iff K).2
      ((QuotientGroup.rightRel_apply).1 hab))

@[simp] theorem rightCosetSet_mk {G : Type*} [Group G]
    (K : Subgroup G) (g : G) :
    rightCosetSet K (rightCoset K g) = MulOpposite.op g • (K : Set G) :=
  rfl

def rightMul {G : Type*} [Group G] (K : Subgroup G)
    (q : RightCosets K) (g : G) : RightCosets K :=
  Quotient.map (fun x => x * g) (by
    intro a b hab
    apply (QuotientGroup.rightRel_apply
      (s := K) (x := a * g) (y := b * g)).2
    have hab' : b * a⁻¹ ∈ K :=
      (QuotientGroup.rightRel_apply (s := K) (x := a) (y := b)).1 hab
    simpa [mul_assoc] using hab') q

@[simp] theorem rightMul_mk {G : Type*} [Group G]
    (K : Subgroup G) (x g : G) :
    rightMul K (rightCoset K x) g = rightCoset K (x * g) :=
  rfl

@[simp] theorem rightMul_one {G : Type*} [Group G]
    (K : Subgroup G) (q : RightCosets K) :
    rightMul K q 1 = q := by
  induction q using Quotient.inductionOn
  apply Quotient.sound
  apply (QuotientGroup.rightRel_apply (s := K)).2
  simp

theorem rightMul_mul {G : Type*} [Group G]
    (K : Subgroup G) (q : RightCosets K) (g h : G) :
    rightMul K q (g * h) = rightMul K (rightMul K q g) h := by
  induction q using Quotient.inductionOn
  apply Quotient.sound
  apply (QuotientGroup.rightRel_apply (s := K)).2
  simp [mul_assoc]

def Vertex : Type u :=
  RightCosets (Mbar S) ⊕ RightCosets (Hbar S)

def mVertex (g : FreeAmalgam S) : Vertex S :=
  Sum.inl (rightCoset (Mbar S) g)

def hVertex (g : FreeAmalgam S) : Vertex S :=
  Sum.inr (rightCoset (Hbar S) g)

def act (g : FreeAmalgam S) : Vertex S → Vertex S
  | Sum.inl q => Sum.inl (rightMul (Mbar S) q g)
  | Sum.inr q => Sum.inr (rightMul (Hbar S) q g)

@[simp] theorem act_mVertex (g x : FreeAmalgam S) :
    act S g (mVertex S x) = mVertex S (x * g) :=
  rfl

@[simp] theorem act_hVertex (g x : FreeAmalgam S) :
    act S g (hVertex S x) = hVertex S (x * g) :=
  rfl

@[simp] theorem act_one (d : Vertex S) : act S 1 d = d := by
  cases d with
  | inl q => exact congrArg Sum.inl (rightMul_one (Mbar S) q)
  | inr q => exact congrArg Sum.inr (rightMul_one (Hbar S) q)

theorem act_mul (g h : FreeAmalgam S) (d : Vertex S) :
    act S (g * h) d = act S h (act S g d) := by
  cases d with
  | inl q => exact congrArg Sum.inl (rightMul_mul (Mbar S) q g h)
  | inr q => exact congrArg Sum.inr (rightMul_mul (Hbar S) q g h)

def Adjacent : Vertex S → Vertex S → Prop
  | Sum.inl qM, Sum.inr qH =>
      (rightCosetSet (Mbar S) qM ∩ rightCosetSet (Hbar S) qH).Nonempty
  | Sum.inr qH, Sum.inl qM =>
      (rightCosetSet (Hbar S) qH ∩ rightCosetSet (Mbar S) qM).Nonempty
  | _, _ => False

theorem adjacent_symm {d e : Vertex S} :
    Adjacent S d e → Adjacent S e d := by
  cases d <;> cases e <;> simp only [Adjacent]
  · intro h
    exact h
  · rintro ⟨x, hxM, hxH⟩
    exact ⟨x, hxH, hxM⟩
  · rintro ⟨x, hxH, hxM⟩
    exact ⟨x, hxM, hxH⟩
  · intro h
    exact h

def cosetGraph : SimpleGraph (Vertex S) :=
  SimpleGraph.fromRel (Adjacent S)

@[simp] theorem cosetGraph_adj (d e : Vertex S) :
    (cosetGraph S).Adj d e ↔ Adjacent S d e :=
  by
    change d ≠ e ∧ (Adjacent S d e ∨ Adjacent S e d) ↔ Adjacent S d e
    constructor
    · rintro ⟨_, h | h⟩
      · exact h
      · exact adjacent_symm S h
    · intro h
      refine ⟨?_, Or.inl h⟩
      intro hde
      subst e
      cases d <;> simp [Adjacent] at h

private theorem rightCoset_inter_nonempty_right_mul_iff
    {G : Type*} [Group G] (K L : Subgroup G) (x y g : G) :
    ((MulOpposite.op (x * g) • (K : Set G)) ∩
      (MulOpposite.op (y * g) • (L : Set G))).Nonempty ↔
    ((MulOpposite.op x • (K : Set G)) ∩
      (MulOpposite.op y • (L : Set G))).Nonempty := by
  constructor
  · rintro ⟨z, hzK, hzL⟩
    refine ⟨z * g⁻¹, ?_, ?_⟩
    · rw [mem_rightCoset_iff] at hzK ⊢
      simpa [mul_assoc] using hzK
    · rw [mem_rightCoset_iff] at hzL ⊢
      simpa [mul_assoc] using hzL
  · rintro ⟨z, hzK, hzL⟩
    refine ⟨z * g, ?_, ?_⟩
    · rw [mem_rightCoset_iff] at hzK ⊢
      simpa [mul_assoc] using hzK
    · rw [mem_rightCoset_iff] at hzL ⊢
      simpa [mul_assoc] using hzL

theorem adjacent_act_iff (g : FreeAmalgam S) (d e : Vertex S) :
    Adjacent S (act S g d) (act S g e) ↔ Adjacent S d e := by
  cases d with
  | inl qM =>
      cases e with
      | inl qM' => rfl
      | inr qH =>
          induction qM using Quotient.inductionOn
          induction qH using Quotient.inductionOn
          exact rightCoset_inter_nonempty_right_mul_iff (Mbar S) (Hbar S) _ _ g
  | inr qH =>
      cases e with
      | inl qM =>
          induction qH using Quotient.inductionOn
          induction qM using Quotient.inductionOn
          exact rightCoset_inter_nonempty_right_mul_iff (Hbar S) (Mbar S) _ _ g
      | inr qH' => rfl

theorem adjacent_m_h_iff_exists_common
    (qM : RightCosets (Mbar S)) (qH : RightCosets (Hbar S)) :
    Adjacent S (Sum.inl qM) (Sum.inr qH) ↔
      ∃ z : FreeAmalgam S,
        qM = rightCoset (Mbar S) z ∧ qH = rightCoset (Hbar S) z := by
  induction qM using Quotient.inductionOn
  induction qH using Quotient.inductionOn
  rename_i x y
  constructor
  · rintro ⟨z, hzM, hzH⟩
    refine ⟨z, ?_, ?_⟩
    · apply Quotient.sound
      apply (QuotientGroup.rightRel_apply (s := Mbar S)).2
      exact (mem_rightCoset_iff x).1 hzM
    · apply Quotient.sound
      apply (QuotientGroup.rightRel_apply (s := Hbar S)).2
      exact (mem_rightCoset_iff y).1 hzH
  · rintro ⟨z, hxz, hyz⟩
    rw [hxz, hyz]
    refine ⟨z, ?_, ?_⟩
    · change z ∈ MulOpposite.op z • (Mbar S : Set (FreeAmalgam S))
      simpa using mem_rightCoset z (show (1 : FreeAmalgam S) ∈ Mbar S by simp)
    · change z ∈ MulOpposite.op z • (Hbar S : Set (FreeAmalgam S))
      simpa using mem_rightCoset z (show (1 : FreeAmalgam S) ∈ Hbar S by simp)

theorem adjacent_iff_exists_common (d e : Vertex S) :
    Adjacent S d e ↔
      ∃ z : FreeAmalgam S,
        (d = mVertex S z ∧ e = hVertex S z) ∨
        (d = hVertex S z ∧ e = mVertex S z) := by
  cases d with
  | inl qM =>
      cases e with
      | inl qM' => simp [Adjacent, mVertex, hVertex]
      | inr qH =>
          constructor
          · intro h
            rcases (adjacent_m_h_iff_exists_common S qM qH).1 h with
              ⟨z, hzM, hzH⟩
            exact ⟨z, Or.inl ⟨congrArg Sum.inl hzM, congrArg Sum.inr hzH⟩⟩
          · rintro ⟨z, hz⟩
            rcases hz with hz | hz
            · exact (adjacent_m_h_iff_exists_common S qM qH).2
                ⟨z, Sum.inl.inj hz.1, Sum.inr.inj hz.2⟩
            · cases hz.1
  | inr qH =>
      cases e with
      | inl qM =>
          constructor
          · intro h
            rcases (adjacent_m_h_iff_exists_common S qM qH).1
              (adjacent_symm S h) with ⟨z, hzM, hzH⟩
            exact ⟨z, Or.inr ⟨congrArg Sum.inr hzH, congrArg Sum.inl hzM⟩⟩
          · rintro ⟨z, hz⟩
            rcases hz with hz | hz
            · cases hz.1
            · exact adjacent_symm S <|
                (adjacent_m_h_iff_exists_common S qM qH).2
                  ⟨z, Sum.inl.inj hz.2, Sum.inr.inj hz.1⟩
      | inr qH' => simp [Adjacent, mVertex, hVertex]

theorem edge_transitive
    {d e d' e' : Vertex S}
    (hde : Adjacent S d e) (hde' : Adjacent S d' e') :
    ∃ g : FreeAmalgam S,
      (act S g d = d' ∧ act S g e = e') ∨
      (act S g d = e' ∧ act S g e = d') := by
  rcases (adjacent_iff_exists_common S d e).1 hde with ⟨x, hx | hx⟩
  · rcases hx with ⟨rfl, rfl⟩
    rcases (adjacent_iff_exists_common S d' e').1 hde' with ⟨y, hy | hy⟩
    · rcases hy with ⟨rfl, rfl⟩
      refine ⟨x⁻¹ * y, Or.inl ⟨?_, ?_⟩⟩ <;> simp
    · rcases hy with ⟨rfl, rfl⟩
      refine ⟨x⁻¹ * y, Or.inr ⟨?_, ?_⟩⟩ <;> simp
  · rcases hx with ⟨rfl, rfl⟩
    rcases (adjacent_iff_exists_common S d' e').1 hde' with ⟨y, hy | hy⟩
    · rcases hy with ⟨rfl, rfl⟩
      refine ⟨x⁻¹ * y, Or.inr ⟨?_, ?_⟩⟩ <;> simp
    · rcases hy with ⟨rfl, rfl⟩
      refine ⟨x⁻¹ * y, Or.inl ⟨?_, ?_⟩⟩ <;> simp

def color : Vertex S → Bool
  | Sum.inl _ => false
  | Sum.inr _ => true

theorem adjacent_color_ne {d e : Vertex S} (h : Adjacent S d e) :
    color S d ≠ color S e := by
  cases d <;> cases e <;> simp_all [Adjacent, color]

theorem action_preserves_color (g : FreeAmalgam S) (d : Vertex S) :
    color S (act S g d) = color S d := by
  cases d <;> rfl

theorem not_vertex_transitive :
    ¬ (∀ d e : Vertex S, ∃ g : FreeAmalgam S, act S g d = e) := by
  intro h
  rcases h (mVertex S 1) (hVertex S 1) with ⟨g, hg⟩
  have hc := action_preserves_color S g (mVertex S 1)
  rw [hg] at hc
  exact Bool.noConfusion hc

def stabilizer (d : Vertex S) : Subgroup (FreeAmalgam S) where
  carrier := {g | act S g d = d}
  one_mem' := act_one S d
  mul_mem' := by
    intro g h hg hh
    change act S g d = d at hg
    change act S h d = d at hh
    change act S (g * h) d = d
    rw [act_mul, hg, hh]
  inv_mem' := by
    intro g hg
    change act S g d = d at hg
    change act S g⁻¹ d = d
    calc
      act S g⁻¹ d = act S g⁻¹ (act S g d) := congrArg (act S g⁻¹) hg.symm
      _ = act S (g * g⁻¹) d := (act_mul S g g⁻¹ d).symm
      _ = d := by simp

/-- The source's `G_d⁽¹⁾`: elements of the vertex stabilizer which also
fix every neighbor of `d`. -/
def neighborhoodKernel (d : Vertex S) : Subgroup (FreeAmalgam S) where
  carrier := {g |
    g ∈ stabilizer S d ∧
      ∀ e : Vertex S, Adjacent S d e → g ∈ stabilizer S e}
  one_mem' := ⟨(stabilizer S d).one_mem, fun e _ => (stabilizer S e).one_mem⟩
  mul_mem' := by
    rintro g h ⟨hgd, hg⟩ ⟨hhd, hh⟩
    exact ⟨(stabilizer S d).mul_mem hgd hhd,
      fun e he => (stabilizer S e).mul_mem (hg e he) (hh e he)⟩
  inv_mem' := by
    rintro g ⟨hgd, hg⟩
    exact ⟨(stabilizer S d).inv_mem hgd,
      fun e he => (stabilizer S e).inv_mem (hg e he)⟩

@[simp] theorem mem_neighborhoodKernel_iff
    (g : FreeAmalgam S) (d : Vertex S) :
    g ∈ neighborhoodKernel S d ↔
      g ∈ stabilizer S d ∧
        ∀ e : Vertex S, Adjacent S d e → g ∈ stabilizer S e :=
  Iff.rfl

theorem stabilizer_m_base :
    stabilizer S (mVertex S 1) = Mbar S := by
  apply SetLike.coe_injective
  change {g | act S g (mVertex S 1) = mVertex S 1} = (Mbar S : Set _)
  ext g
  simp only [Set.mem_ofPred_eq]
  rw [act_mVertex]
  simp only [one_mul]
  change mVertex S g = mVertex S 1 ↔ g ∈ Mbar S
  constructor
  · intro hg
    have hq : rightCoset (Mbar S) g = rightCoset (Mbar S) 1 :=
      Sum.inl.inj hg
    have hr : QuotientGroup.rightRel (Mbar S) g 1 :=
      Quotient.exact hq
    rw [QuotientGroup.rightRel_apply] at hr
    simpa using hr
  · intro hg
    apply congrArg Sum.inl
    apply Quotient.sound
    apply (QuotientGroup.rightRel_apply).2
    simpa using hg

theorem stabilizer_h_base :
    stabilizer S (hVertex S 1) = Hbar S := by
  apply SetLike.coe_injective
  change {g | act S g (hVertex S 1) = hVertex S 1} = (Hbar S : Set _)
  ext g
  simp only [Set.mem_ofPred_eq]
  rw [act_hVertex]
  simp only [one_mul]
  change hVertex S g = hVertex S 1 ↔ g ∈ Hbar S
  constructor
  · intro hg
    have hq : rightCoset (Hbar S) g = rightCoset (Hbar S) 1 :=
      Sum.inr.inj hg
    have hr : QuotientGroup.rightRel (Hbar S) g 1 :=
      Quotient.exact hq
    rw [QuotientGroup.rightRel_apply] at hr
    simpa using hr
  · intro hg
    apply congrArg Sum.inr
    apply Quotient.sound
    apply (QuotientGroup.rightRel_apply).2
    simpa using hg

theorem base_edge_stabilizer :
    stabilizer S (mVertex S 1) ⊓ stabilizer S (hVertex S 1) = Sbar S := by
  rw [stabilizer_m_base, stabilizer_h_base, Mbar_inf_Hbar]

theorem stabilizer_act (g : FreeAmalgam S) (d : Vertex S) :
    stabilizer S (act S g d) =
      (stabilizer S d).map (MulAut.conj g⁻¹).toMonoidHom := by
  ext h
  constructor
  · intro hh
    refine ⟨g * h * g⁻¹, ?_, ?_⟩
    · change act S (g * h * g⁻¹) d = d
      calc
        act S (g * h * g⁻¹) d =
            act S g⁻¹ (act S h (act S g d)) := by
              simp only [act_mul, mul_assoc]
        _ = act S g⁻¹ (act S g d) := congrArg (act S g⁻¹) hh
        _ = d := by rw [← act_mul]; simp
    · simp [mul_assoc]
  · rintro ⟨k, hk, rfl⟩
    change act S ((MulAut.conj g⁻¹) k) (act S g d) = act S g d
    rw [MulAut.conj_apply]
    simp only [inv_inv]
    change act S (g⁻¹ * k * g) (act S g d) = act S g d
    calc
      act S (g⁻¹ * k * g) (act S g d) =
          act S (g * (g⁻¹ * k * g)) d := by rw [← act_mul]
      _ = act S (k * g) d := by simp [mul_assoc]
      _ = act S g (act S k d) := by rw [act_mul]
      _ = act S g d := congrArg (act S g) hk

theorem stabilizer_mVertex (x : FreeAmalgam S) :
    stabilizer S (mVertex S x) =
      (Mbar S).map (MulAut.conj x⁻¹).toMonoidHom := by
  calc
    stabilizer S (mVertex S x) =
        stabilizer S (act S x (mVertex S 1)) := by
          rw [act_mVertex, one_mul]
    _ = (stabilizer S (mVertex S 1)).map
          (MulAut.conj x⁻¹).toMonoidHom := stabilizer_act S x (mVertex S 1)
    _ = (Mbar S).map (MulAut.conj x⁻¹).toMonoidHom := by
          rw [stabilizer_m_base]

theorem stabilizer_hVertex (x : FreeAmalgam S) :
    stabilizer S (hVertex S x) =
      (Hbar S).map (MulAut.conj x⁻¹).toMonoidHom := by
  calc
    stabilizer S (hVertex S x) =
        stabilizer S (act S x (hVertex S 1)) := by
          rw [act_hVertex, one_mul]
    _ = (stabilizer S (hVertex S 1)).map
          (MulAut.conj x⁻¹).toMonoidHom := stabilizer_act S x (hVertex S 1)
    _ = (Hbar S).map (MulAut.conj x⁻¹).toMonoidHom := by
          rw [stabilizer_h_base]

theorem stabilizer_conjugate_factor (d : Vertex S) :
    (∃ x : FreeAmalgam S,
      stabilizer S d = (Mbar S).map (MulAut.conj x).toMonoidHom) ∨
    (∃ x : FreeAmalgam S,
      stabilizer S d = (Hbar S).map (MulAut.conj x).toMonoidHom) := by
  cases d with
  | inl qM =>
      induction qM using Quotient.inductionOn
      change
        (∃ x : FreeAmalgam S,
          stabilizer S (mVertex S _) =
            (Mbar S).map (MulAut.conj x).toMonoidHom) ∨ _
      exact Or.inl ⟨_⁻¹, by simpa using stabilizer_mVertex S _⟩
  | inr qH =>
      induction qH using Quotient.inductionOn
      change
        _ ∨ (∃ x : FreeAmalgam S,
          stabilizer S (hVertex S _) =
            (Hbar S).map (MulAut.conj x).toMonoidHom)
      exact Or.inr ⟨_⁻¹, by simpa using stabilizer_hVertex S _⟩

theorem base_adjacent : Adjacent S (mVertex S 1) (hVertex S 1) := by
  refine ⟨1, ?_, ?_⟩
  · change 1 ∈ MulOpposite.op 1 • (Mbar S : Set (FreeAmalgam S))
    simp
  · change 1 ∈ MulOpposite.op 1 • (Hbar S : Set (FreeAmalgam S))
    simp

def Neighbor (d : Vertex S) : Type u :=
  {e : Vertex S // Adjacent S d e}

private def neighborFromM (x : FreeAmalgam S) (m : M) :
    Neighbor S (mVertex S x) := by
  refine ⟨hVertex S (embedM S m * x), ?_⟩
  apply (adjacent_m_h_iff_exists_common S _ _).2
  refine ⟨embedM S m * x, ?_, rfl⟩
  apply Quotient.sound
  apply (QuotientGroup.rightRel_apply (s := Mbar S)).2
  simpa [mul_assoc] using (show embedM S m ∈ Mbar S from ⟨m, rfl⟩)

private theorem neighborFromM_surjective [Finite M] (x : FreeAmalgam S) :
    Function.Surjective (neighborFromM S x) := by
  rintro ⟨e, he⟩
  cases e with
  | inl qM => simp [Adjacent, mVertex] at he
  | inr qH =>
      rcases (adjacent_m_h_iff_exists_common S _ _).1 he with ⟨z, hxz, hqz⟩
      have hzM : z * x⁻¹ ∈ Mbar S :=
        (QuotientGroup.rightRel_apply (s := Mbar S)).1
          ((Quotient.eq_iff_equiv).1 hxz)
      rcases hzM with ⟨m, hm⟩
      have hmz : embedM S m * x = z := by
        calc
          embedM S m * x = (z * x⁻¹) * x := by rw [hm]
          _ = z := by simp [mul_assoc]
      refine ⟨m, ?_⟩
      apply Subtype.ext
      change hVertex S (embedM S m * x) = Sum.inr qH
      rw [hmz]
      exact (congrArg Sum.inr hqz).symm

theorem finite_neighbors_m [Finite M] (x : FreeAmalgam S) :
    Finite (Neighbor S (mVertex S x)) :=
  Finite.of_surjective (neighborFromM S x) (neighborFromM_surjective S x)

private def neighborFromH (x : FreeAmalgam S) (h : Holomorph S) :
    Neighbor S (hVertex S x) := by
  refine ⟨mVertex S (embedH S h * x), ?_⟩
  apply adjacent_symm S
  apply (adjacent_m_h_iff_exists_common S _ _).2
  refine ⟨embedH S h * x, rfl, ?_⟩
  apply Quotient.sound
  apply (QuotientGroup.rightRel_apply (s := Hbar S)).2
  simpa [mul_assoc] using (show embedH S h ∈ Hbar S from ⟨h, rfl⟩)

private theorem neighborFromH_surjective [Finite M] (x : FreeAmalgam S) :
    Function.Surjective (neighborFromH S x) := by
  rintro ⟨e, he⟩
  cases e with
  | inl qM =>
      rcases (adjacent_m_h_iff_exists_common S _ _).1
        (adjacent_symm S he) with ⟨z, hqz, hxz⟩
      have hzH : z * x⁻¹ ∈ Hbar S :=
        (QuotientGroup.rightRel_apply (s := Hbar S)).1
          ((Quotient.eq_iff_equiv).1 hxz)
      rcases hzH with ⟨h, hh⟩
      have hhz : embedH S h * x = z := by
        calc
          embedH S h * x = (z * x⁻¹) * x := by rw [hh]
          _ = z := by simp [mul_assoc]
      refine ⟨h, ?_⟩
      apply Subtype.ext
      change mVertex S (embedH S h * x) = Sum.inl qM
      rw [hhz]
      exact (congrArg Sum.inl hqz).symm
  | inr qH => simp [Adjacent, hVertex] at he

theorem finite_neighbors_h [Finite M] (x : FreeAmalgam S) :
    Finite (Neighbor S (hVertex S x)) :=
  Finite.of_surjective (neighborFromH S x) (neighborFromH_surjective S x)

theorem finite_neighbors [Finite M] (d : Vertex S) :
    Finite (Neighbor S d) := by
  cases d with
  | inl qM =>
      induction qM using Quotient.inductionOn
      exact finite_neighbors_m S _
  | inr qH =>
      induction qH using Quotient.inductionOn
      exact finite_neighbors_h S _

/-! ## Local transitivity -/

private theorem stabilizer_transitive_neighbors_m [Finite M]
    (x : FreeAmalgam S) {e f : Vertex S}
    (he : Adjacent S (mVertex S x) e)
    (hf : Adjacent S (mVertex S x) f) :
    ∃ g : FreeAmalgam S,
      g ∈ stabilizer S (mVertex S x) ∧ act S g e = f := by
  rcases neighborFromM_surjective S x ⟨e, he⟩ with ⟨m, hm⟩
  rcases neighborFromM_surjective S x ⟨f, hf⟩ with ⟨n, hn⟩
  refine ⟨(MulAut.conj x⁻¹) (embedM S (m⁻¹ * n)), ?_, ?_⟩
  · rw [stabilizer_mVertex]
    refine ⟨embedM S (m⁻¹ * n), ⟨m⁻¹ * n, rfl⟩, rfl⟩
  · have hme := congrArg Subtype.val hm
    have hnf := congrArg Subtype.val hn
    change hVertex S (embedM S m * x) = e at hme
    change hVertex S (embedM S n * x) = f at hnf
    rw [← hme, ← hnf]
    simp [map_mul, mul_assoc]

private theorem stabilizer_transitive_neighbors_h [Finite M]
    (x : FreeAmalgam S) {e f : Vertex S}
    (he : Adjacent S (hVertex S x) e)
    (hf : Adjacent S (hVertex S x) f) :
    ∃ g : FreeAmalgam S,
      g ∈ stabilizer S (hVertex S x) ∧ act S g e = f := by
  rcases neighborFromH_surjective S x ⟨e, he⟩ with ⟨h, hm⟩
  rcases neighborFromH_surjective S x ⟨f, hf⟩ with ⟨k, hn⟩
  refine ⟨(MulAut.conj x⁻¹) (embedH S (h⁻¹ * k)), ?_, ?_⟩
  · rw [stabilizer_hVertex]
    refine ⟨embedH S (h⁻¹ * k), ⟨h⁻¹ * k, rfl⟩, rfl⟩
  · have hme := congrArg Subtype.val hm
    have hnf := congrArg Subtype.val hn
    change mVertex S (embedH S h * x) = e at hme
    change mVertex S (embedH S k * x) = f at hnf
    rw [← hme, ← hnf]
    simp [map_mul, mul_assoc]

theorem stabilizer_transitive_neighbors [Finite M]
    (d : Vertex S) {e f : Vertex S}
    (he : Adjacent S d e) (hf : Adjacent S d f) :
    ∃ g : FreeAmalgam S, g ∈ stabilizer S d ∧ act S g e = f := by
  cases d with
  | inl qM =>
      induction qM using Quotient.inductionOn
      exact stabilizer_transitive_neighbors_m S _ he hf
  | inr qH =>
      induction qH using Quotient.inductionOn
      exact stabilizer_transitive_neighbors_h S _ he hf

/-! ## Connectedness -/

private abbrev Connected (d e : Vertex S) : Prop :=
  Relation.ReflTransGen (Adjacent S) d e

private theorem connected_action (g : FreeAmalgam S) {d e : Vertex S}
    (h : Connected S d e) :
    Connected S (act S g d) (act S g e) := by
  exact h.lift (act S g) fun _ _ hde => (adjacent_act_iff S g _ _).2 hde

private theorem mVertex_embedM_eq_base (m : M) :
    mVertex S (embedM S m) = mVertex S 1 := by
  apply congrArg Sum.inl
  apply Quotient.sound
  apply (QuotientGroup.rightRel_apply).2
  simpa using (show embedM S m ∈ Mbar S from ⟨m, rfl⟩)

private theorem hVertex_embedH_eq_base (h : Holomorph S) :
    hVertex S (embedH S h) = hVertex S 1 := by
  apply congrArg Sum.inr
  apply Quotient.sound
  apply (QuotientGroup.rightRel_apply).2
  simpa using (show embedH S h ∈ Hbar S from ⟨h, rfl⟩)

private theorem mVertex_embedS_eq_base (s : S) :
    mVertex S (embedS S s) = mVertex S 1 := by
  rw [← embedM_comp_subtype S]
  exact mVertex_embedM_eq_base S s

private theorem hVertex_embedS_eq_base (s : S) :
    hVertex S (embedS S s) = hVertex S 1 := by
  rw [← embedH_comp_inl S]
  exact hVertex_embedH_eq_base S (SemidirectProduct.inl s)

private theorem base_connected_pair (x : FreeAmalgam S) :
    Connected S (mVertex S 1) (mVertex S x) ∧
      Connected S (mVertex S 1) (hVertex S x) := by
  induction x using Monoid.PushoutI.induction_on with
  | of i g =>
      cases i with
      | m =>
          have hm : mVertex S (embedM S g) = mVertex S 1 :=
            mVertex_embedM_eq_base S g
          have hadj : Adjacent S (mVertex S (embedM S g))
              (hVertex S (embedM S g)) :=
            (adjacent_m_h_iff_exists_common S _ _).2
              ⟨embedM S g, rfl, rfl⟩
          refine ⟨hm ▸ Relation.ReflTransGen.refl, ?_⟩
          exact hm ▸ Relation.ReflTransGen.single hadj
      | h =>
          have hh : hVertex S (embedH S g) = hVertex S 1 :=
            hVertex_embedH_eq_base S g
          have hadj : Adjacent S (mVertex S (embedH S g))
              (hVertex S (embedH S g)) :=
            (adjacent_m_h_iff_exists_common S _ _).2
              ⟨embedH S g, rfl, rfl⟩
          refine ⟨?_, hh ▸ Relation.ReflTransGen.single (base_adjacent S)⟩
          exact (Relation.ReflTransGen.single (base_adjacent S)).tail
            (hh ▸ adjacent_symm S hadj)
  | base s =>
      have hm : mVertex S (embedS S s) = mVertex S 1 :=
        mVertex_embedS_eq_base S s
      have hh : hVertex S (embedS S s) = hVertex S 1 :=
        hVertex_embedS_eq_base S s
      exact ⟨hm ▸ Relation.ReflTransGen.refl,
        hh ▸ Relation.ReflTransGen.single (base_adjacent S)⟩
  | mul x y hx hy =>
      rcases hx with ⟨hxm, hxh⟩
      rcases hy with ⟨hym, _hyh⟩
      have hxm_y := connected_action S y hxm
      have hxh_y := connected_action S y hxh
      have hxm_y' : Connected S (mVertex S y) (mVertex S (x * y)) := by
        simpa using hxm_y
      have hxh_y' : Connected S (mVertex S y) (hVertex S (x * y)) := by
        simpa using hxh_y
      exact ⟨hym.trans hxm_y', hym.trans hxh_y'⟩

theorem connected (d e : Vertex S) :
    Relation.ReflTransGen (Adjacent S) d e := by
  have hbase (v : Vertex S) : Connected S (mVertex S 1) v := by
    cases v with
    | inl qM =>
        induction qM using Quotient.inductionOn
        exact (base_connected_pair S _).1
    | inr qH =>
        induction qH using Quotient.inductionOn
        exact (base_connected_pair S _).2
  have reverse {v : Vertex S} (h : Connected S (mVertex S 1) v) :
      Connected S v (mVertex S 1) := by
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail hxy hyz ih =>
        exact (Relation.ReflTransGen.single (adjacent_symm S hyz)).trans ih
  exact (reverse (hbase d)).trans (hbase e)

theorem cosetGraph_connected : (cosetGraph S).Connected := by
  let _ : Nonempty (Vertex S) := ⟨mVertex S 1⟩
  constructor
  intro d e
  rw [SimpleGraph.reachable_iff_reflTransGen]
  exact Relation.ReflTransGen.mono
    (fun a b h => (cosetGraph_adj S a b).2 h) d e (connected S d e)

/-! ## Faithfulness -/

def actionKernel : Subgroup (FreeAmalgam S) where
  carrier := {g | ∀ d : Vertex S, act S g d = d}
  one_mem' := act_one S
  mul_mem' := by
    intro g h hg hh d
    rw [act_mul, hg, hh]
  inv_mem' := by
    intro g hg d
    calc
      act S g⁻¹ d = act S g⁻¹ (act S g d) := congrArg (act S g⁻¹) (hg d).symm
      _ = act S (g * g⁻¹) d := (act_mul S g g⁻¹ d).symm
      _ = d := by simp

theorem actionKernel_normal : (actionKernel S).Normal := by
  constructor
  intro n hn g d
  change act S (g * n * g⁻¹) d = d
  calc
    act S (g * n * g⁻¹) d = act S g⁻¹ (act S n (act S g d)) := by
      simp only [act_mul, mul_assoc]
    _ = act S g⁻¹ (act S g d) := congrArg (act S g⁻¹) (hn (act S g d))
    _ = d := by rw [← act_mul]; simp

theorem actionKernel_eq_bot [Finite M]
    (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal) :
    actionKernel S = ⊥ := by
  let K := actionKernel S
  have hKM : K ≤ Mbar S := by
    rw [← stabilizer_m_base S]
    exact fun _ hk => hk (mVertex S 1)
  have hKH : K ≤ Hbar S := by
    rw [← stabilizer_h_base S]
    exact fun _ hk => hk (hVertex S 1)
  have hKS : K ≤ Sbar S := by
    rw [← Mbar_inf_Hbar S]
    exact le_inf hKM hKH
  have hKN : K.Normal := actionKernel_normal S
  exact no_nontrivial_common_invariant S T hTS hP K hKS
    (fun k hk n hn => hKN.conj_mem n hn k)
    (fun k hk n hn => hKN.conj_mem n hn k)

end Stellmacher.PushingUp.AmalgamGraph
