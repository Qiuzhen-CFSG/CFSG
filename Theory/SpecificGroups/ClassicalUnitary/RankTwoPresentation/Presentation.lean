module
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.Faithfulness
public import Mathlib.GroupTheory.PresentedGroup

/-!
# An explicit relative unitary Bruhat presentation

The generators are the four positive parameter groups, the full torus,
and the two marked reflections. The relations are precisely the internal
group laws, six positive crossings, four torus actions, Weyl conjugations,
involutions, braid relation, and two nonzero rank-one equations. Parameter
formulas are supplied by `Parameters`; no model multiplication table occurs.

The quotient by the normal closure of these relations satisfies them and
has eight-cell Bruhat coverage. Its evaluation is constructed by the universal
property. Collected-coordinate injectivity and Weyl separation prove its
faithfulness; generation proves its surjectivity. The concrete unitary modules
supply those independent checks. Source: Steinberg, Lectures on Chevalley
Groups, Lemmas 21–26 and the proof mechanism of Theorem 9, adapted using
Theorem 33 / Lemmas 63–64 for the relative unitary roots.
-/
@[expose] public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
namespace Presentation
variable {RA RD RC RB H : Type*} [Group RA] [Group RD] [Group RC] [Group RB] [Group H]

inductive Generator (RA RD RC RB H : Type*)
  | A : RA → Generator RA RD RC RB H
  | D : RD → Generator RA RD RC RB H
  | C : RC → Generator RA RD RC RB H
  | B : RB → Generator RA RD RC RB H
  | torus : H → Generator RA RD RC RB H
  | s | t

def Generator.ofMaps {M : Type*} [Group M] (r : PositiveMaps M RA RD RC RB)
    (h : H →* M) (s t : M) : Generator RA RD RC RB H → M
  | .A a => r.A a | .D d => r.D d | .C c => r.C c | .B b => r.B b
  | .torus k => h k | .s => s | .t => t

/-- Parameter formulas for the finite list of unitary relation schemes. -/
structure Parameters (RA RD RC RB H : Type*) [Group RA] [Group RD] [Group RC] [Group RB] [Group H] where
  ca : RC → RA → RD
  bd : RB → RD → RC
  baD : RB → RA → RD
  baC : RB → RA → RC
  hA : H → RA → RA
  hD : H → RD → RD
  hC : H → RC → RC
  hB : H → RB → RB
  sh : H → H
  th : H → H
  sD : RD → RB
  sC : RC → RC
  sB : RB → RD
  tA : RA → RC
  tD : RD → RD
  tC : RC → RA
  rankA : (a : RA) → a≠1 → RA × H × RA
  rankB : (b : RB) → b≠1 → RB × H × RB

local notation "F" => FreeGroup (Generator RA RD RC RB H)
abbrev a (x : RA) : F := FreeGroup.of (.A x)
abbrev d (x : RD) : F := FreeGroup.of (.D x)
abbrev c (x : RC) : F := FreeGroup.of (.C x)
abbrev b (x : RB) : F := FreeGroup.of (.B x)
abbrev h (x : H) : F := FreeGroup.of (.torus x)
abbrev s : F := FreeGroup.of .s
abbrev t : F := FreeGroup.of .t

/-- Only root group laws, positive crossings, torus actions, Weyl equations,
and the two nonzero rank-one equations occur in this presentation. -/
inductive Equation (p : Parameters RA RD RC RB H) : F → F → Prop
  | aOne : Equation p (a 1) 1
  | dOne : Equation p (d 1) 1
  | cOne : Equation p (c 1) 1
  | bOne : Equation p (b 1) 1
  | hOne : Equation p (h 1) 1
  | aMul (x y : RA) : Equation p (a (x*y)) (a x*a y)
  | dMul (x y : RD) : Equation p (d (x*y)) (d x*d y)
  | cMul (x y : RC) : Equation p (c (x*y)) (c x*c y)
  | bMul (x y : RB) : Equation p (b (x*y)) (b x*b y)
  | hMul (x y : H) : Equation p (h (x*y)) (h x*h y)
  | ad (x y) : Equation p (a x*d y) (d y*a x)
  | cd (x y) : Equation p (c x*d y) (d y*c x)
  | bc (x y) : Equation p (b x*c y) (c y*b x)
  | ca (x y) : Equation p (c x*a y) (a y*d (p.ca x y)*c x)
  | bd (x y) : Equation p (b x*d y) (d y*c (p.bd x y)*b x)
  | ba (x y) : Equation p (b x*a y) (a y*d (p.baD x y)*c (p.baC x y)*b x)
  | ha (k x) : Equation p (h k*a x*(h k)⁻¹) (a (p.hA k x))
  | hd (k x) : Equation p (h k*d x*(h k)⁻¹) (d (p.hD k x))
  | hc (k x) : Equation p (h k*c x*(h k)⁻¹) (c (p.hC k x))
  | hb (k x) : Equation p (h k*b x*(h k)⁻¹) (b (p.hB k x))
  | ss : Equation p (s*s) 1
  | tt : Equation p (t*t) 1
  | st : Equation p ((s*t)^4) 1
  | sh (k) : Equation p (s*h k*s) (h (p.sh k))
  | th (k) : Equation p (t*h k*t) (h (p.th k))
  | sd (x) : Equation p (s*d x*s) (b (p.sD x))
  | sc (x) : Equation p (s*c x*s) (c (p.sC x))
  | sb (x) : Equation p (s*b x*s) (d (p.sB x))
  | ta (x) : Equation p (t*a x*t) (c (p.tA x))
  | td (x) : Equation p (t*d x*t) (d (p.tD x))
  | tc (x) : Equation p (t*c x*t) (a (p.tC x))
  | sa (x) (hx : x≠1) : Equation p (s*a x*s)
      (a (p.rankA x hx).1*h (p.rankA x hx).2.1*s*a (p.rankA x hx).2.2)
  | tb (x) (hx : x≠1) : Equation p (t*b x*t)
      (b (p.rankB x hx).1*h (p.rankB x hx).2.1*t*b (p.rankB x hx).2.2)

namespace Parameters
variable (p : Parameters RA RD RC RB H)
def relators : Set F := {z | ∃ x y, Equation p x y ∧ z=x*y⁻¹}
abbrev Carrier := PresentedGroup p.relators

variable {M : Type*} [Group M]
def Satisfies (g : Generator RA RD RC RB H → M) : Prop :=
  ∀ x y, Equation p x y → FreeGroup.lift g x=FreeGroup.lift g y

namespace Satisfies
variable {p} {g : Generator RA RD RC RB H → M} (hg : p.Satisfies g)

def roots : PositiveMaps M RA RD RC RB where
  A := { toFun := fun x => g (.A x)
         map_one' := by simpa using hg _ _ .aOne
         map_mul' := fun x y => by simpa using hg _ _ (.aMul x y) }
  D := { toFun := fun x => g (.D x)
         map_one' := by simpa using hg _ _ .dOne
         map_mul' := fun x y => by simpa using hg _ _ (.dMul x y) }
  C := { toFun := fun x => g (.C x)
         map_one' := by simpa using hg _ _ .cOne
         map_mul' := fun x y => by simpa using hg _ _ (.cMul x y) }
  B := { toFun := fun x => g (.B x)
         map_one' := by simpa using hg _ _ .bOne
         map_mul' := fun x y => by simpa using hg _ _ (.bMul x y) }

def torus : H →* M where
  toFun := fun x => g (.torus x)
  map_one' := by simpa using hg _ _ .hOne
  map_mul' := fun x y => by simpa using hg _ _ (.hMul x y)

theorem collects : hg.roots.Collects where
  AD x y := by simpa [roots,Commute,SemiconjBy] using hg _ _ (.ad x y)
  CD x y := by simpa [roots,Commute,SemiconjBy] using hg _ _ (.cd x y)
  BC x y := by simpa [roots,Commute,SemiconjBy] using hg _ _ (.bc x y)
  CA x y := ⟨p.ca x y,by simpa [roots] using hg _ _ (.ca x y)⟩
  BD x y := ⟨p.bd x y,by simpa [roots] using hg _ _ (.bd x y)⟩
  BA x y := ⟨p.baD x y,p.baC x y,by simpa [roots] using hg _ _ (.ba x y)⟩

theorem torusLaws : hg.roots.TorusLaws hg.torus where
  A k x := ⟨p.hA k x,by simpa [roots,torus] using hg _ _ (.ha k x)⟩
  D k x := ⟨p.hD k x,by simpa [roots,torus] using hg _ _ (.hd k x)⟩
  C k x := ⟨p.hC k x,by simpa [roots,torus] using hg _ _ (.hc k x)⟩
  B k x := ⟨p.hB k x,by simpa [roots,torus] using hg _ _ (.hb k x)⟩

theorem reflections : ReflectionLaws hg.roots hg.torus (g .s) (g .t) where
  ss := by simpa using hg _ _ .ss
  tt := by simpa using hg _ _ .tt
  sD x := ⟨p.sD x,by simpa [roots] using hg _ _ (.sd x)⟩
  sC x := ⟨p.sC x,by simpa [roots] using hg _ _ (.sc x)⟩
  sB x := ⟨p.sB x,by simpa [roots] using hg _ _ (.sb x)⟩
  tA x := ⟨p.tA x,by simpa [roots] using hg _ _ (.ta x)⟩
  tD x := ⟨p.tD x,by simpa [roots] using hg _ _ (.td x)⟩
  tC x := ⟨p.tC x,by simpa [roots] using hg _ _ (.tc x)⟩
  sA x := by
    by_cases hx : x=1
    · left; subst x
      simpa [roots,show g (.A 1)=1 from hg.roots.A.map_one] using hg _ _ .ss
    · exact Or.inr ⟨(p.rankA x hx).1,(p.rankA x hx).2.1,(p.rankA x hx).2.2,
        by simpa [roots,torus] using hg _ _ (.sa x hx)⟩
  tB x := by
    by_cases hx : x=1
    · left; subst x
      simpa [roots,show g (.B 1)=1 from hg.roots.B.map_one] using hg _ _ .tt
    · exact Or.inr ⟨(p.rankB x hx).1,(p.rankB x hx).2.1,(p.rankB x hx).2.2,
        by simpa [roots,torus] using hg _ _ (.tb x hx)⟩

theorem s_torus (k : H) : g .s*hg.torus k*g .s=hg.torus (p.sh k) := by
  simpa [torus] using hg _ _ (.sh k)
theorem t_torus (k : H) : g .t*hg.torus k*g .t=hg.torus (p.th k) := by
  simpa [torus] using hg _ _ (.th k)
include hg in
theorem rotation_four : (g .s*g .t)^4=1 := by simpa using hg _ _ .st
end Satisfies

theorem roots_ofMaps {r : PositiveMaps M RA RD RC RB} {h : H →* M} {s t : M}
    (hp : p.Satisfies (Generator.ofMaps r h s t)) : hp.roots=r := by
  cases r
  rfl

theorem torus_ofMaps {r : PositiveMaps M RA RD RC RB} {h : H →* M} {s t : M}
    (hp : p.Satisfies (Generator.ofMaps r h s t)) : hp.torus=h := rfl

/-- The defining relation schemes hold in the quotient by their normal closure. -/
theorem canonical_satisfies : p.Satisfies (PresentedGroup.of : Generator RA RD RC RB H → p.Carrier) := by
  intro x y hxy
  have he : FreeGroup.lift (PresentedGroup.of : Generator RA RD RC RB H → p.Carrier)=PresentedGroup.mk p.relators := by
    apply FreeGroup.ext_hom
    intro x
    rfl
  rw [he]
  exact PresentedGroup.mk_eq_mk_of_mul_inv_mem ⟨x,y,hxy,rfl⟩

/-- The evaluation homomorphism is constructed from the explicit equation schemes. -/
def evaluate {g : Generator RA RD RC RB H → M} (hg : p.Satisfies g) : p.Carrier →* M :=
  PresentedGroup.toGroup (f := g) (by
    rintro z ⟨x,y,hxy,rfl⟩
    rw [map_mul,map_inv,hg x y hxy,mul_inv_cancel])

@[simp] theorem evaluate_generator {g : Generator RA RD RC RB H → M}
    (hg : p.Satisfies g) (x : Generator RA RD RC RB H) : p.evaluate hg (PresentedGroup.of x)=g x :=
  PresentedGroup.toGroup.of _

theorem canonical_generation : ReflectionLaws.fullGenerated p.canonical_satisfies.roots
    p.canonical_satisfies.torus (PresentedGroup.of .s) (PresentedGroup.of .t)=⊤ := by
  apply top_unique
  intro x hx
  apply PresentedGroup.generated_by
  intro z
  cases z with
  | A x => exact Subgroup.subset_closure (Or.inl (p.canonical_satisfies.roots.A_mem_borel _ x))
  | D x => exact Subgroup.subset_closure (Or.inl (p.canonical_satisfies.roots.D_mem_borel _ x))
  | C x => exact Subgroup.subset_closure (Or.inl (p.canonical_satisfies.roots.C_mem_borel _ x))
  | B x => exact Subgroup.subset_closure (Or.inl (p.canonical_satisfies.roots.B_mem_borel _ x))
  | torus x => exact Subgroup.subset_closure (Or.inl (p.canonical_satisfies.roots.torus_mem_borel _ x))
  | s => exact Subgroup.subset_closure (Or.inr (Or.inl rfl))
  | t => exact Subgroup.subset_closure (Or.inr (Or.inr rfl))

/-- All elements of the newly presented group have one of eight Bruhat words. -/
theorem canonical_eight_cells (x : p.Carrier) : ∃ w : WeylWord,
    InCell (p.canonical_satisfies.roots.borel p.canonical_satisfies.torus)
      (w.eval (PresentedGroup.of .s) (PresentedGroup.of .t)) x := by
  apply p.canonical_satisfies.reflections.exists_cell p.canonical_satisfies.collects
    p.canonical_satisfies.torusLaws
    (fun k => ⟨p.sh k,p.canonical_satisfies.s_torus k⟩)
    (fun k => ⟨p.th k,p.canonical_satisfies.t_torus k⟩)
    p.canonical_satisfies.rotation_four
  rw [p.canonical_generation]
  trivial

@[simp] theorem evaluate_word {g : Generator RA RD RC RB H → M} (hg : p.Satisfies g)
    (a : RA) (d : RD) (c : RC) (b : RB) (k : H) :
    p.evaluate hg (p.canonical_satisfies.roots.word a d c b*p.canonical_satisfies.torus k)=
      hg.roots.word a d c b*hg.torus k := by
  simp [PositiveMaps.word,Satisfies.roots,Satisfies.torus]

theorem evaluate_borel_le {g : Generator RA RD RC RB H → M} (hg : p.Satisfies g) :
    p.canonical_satisfies.roots.borel p.canonical_satisfies.torus ≤
      (hg.roots.borel hg.torus).comap (p.evaluate hg) := by
  apply sup_le
  · apply (Subgroup.closure_le _).mpr
    intro x hx
    rcases hx with ((⟨a,rfl⟩|⟨d,rfl⟩)|⟨c,rfl⟩)|⟨b,rfl⟩
    · change p.evaluate hg (PresentedGroup.of (.A a))∈hg.roots.borel hg.torus
      rw [evaluate_generator]
      exact hg.roots.A_mem_borel _ a
    · change p.evaluate hg (PresentedGroup.of (.D d))∈hg.roots.borel hg.torus
      rw [evaluate_generator]
      exact hg.roots.D_mem_borel _ d
    · change p.evaluate hg (PresentedGroup.of (.C c))∈hg.roots.borel hg.torus
      rw [evaluate_generator]
      exact hg.roots.C_mem_borel _ c
    · change p.evaluate hg (PresentedGroup.of (.B b))∈hg.roots.borel hg.torus
      rw [evaluate_generator]
      exact hg.roots.B_mem_borel _ b
  · rintro x ⟨k,rfl⟩
    change p.evaluate hg (PresentedGroup.of (.torus k))∈hg.roots.borel hg.torus
    rw [evaluate_generator]
    exact hg.roots.torus_mem_borel _ k

/-- Faithfulness of the constructed evaluation, from the two independent
matrix checks. No homomorphism or presentation faithfulness is an input. -/
theorem evaluate_injective {g : Generator RA RD RC RB H → M} (hg : p.Satisfies g)
    (hcoords : Function.Injective (fun q : RA × RD × RC × RB × H =>
      hg.roots.word q.1 q.2.1 q.2.2.1 q.2.2.2.1*hg.torus q.2.2.2.2))
    (hweyl : ∀ w : WeylWord, w.eval (g .s) (g .t)∈hg.roots.borel hg.torus → w=.one) :
    Function.Injective (p.evaluate hg) := by
  have hf := p.canonical_satisfies.reflections.injective_on_fullGenerated
    p.canonical_satisfies.collects p.canonical_satisfies.torusLaws
    (fun k => ⟨p.sh k,p.canonical_satisfies.s_torus k⟩)
    (fun k => ⟨p.th k,p.canonical_satisfies.t_torus k⟩)
    p.canonical_satisfies.rotation_four (p.evaluate hg) (hg.roots.borel hg.torus)
    (p.evaluate_borel_le hg)
    (by intro x y hxy; apply hcoords; simpa only [evaluate_word] using hxy)
    (by intro w hw; apply hweyl w; simpa only [WeylWord.map_eval,evaluate_generator] using hw)
  intro x y hxy
  have hx : x∈ReflectionLaws.fullGenerated p.canonical_satisfies.roots
      p.canonical_satisfies.torus (PresentedGroup.of .s) (PresentedGroup.of .t) := by
    rw [p.canonical_generation]; trivial
  have hy : y∈ReflectionLaws.fullGenerated p.canonical_satisfies.roots
      p.canonical_satisfies.torus (PresentedGroup.of .s) (PresentedGroup.of .t) := by
    rw [p.canonical_generation]; trivial
  exact congrArg Subtype.val (hf (show (p.evaluate hg).comp _ ⟨x,hx⟩=
    (p.evaluate hg).comp _ ⟨y,hy⟩ from hxy))


theorem borel_le_range {g : Generator RA RD RC RB H → M} (hg : p.Satisfies g) :
    hg.roots.borel hg.torus≤(p.evaluate hg).range := by
  apply sup_le
  · apply (Subgroup.closure_le _).mpr
    intro x hx
    rcases hx with ((⟨a,rfl⟩|⟨d,rfl⟩)|⟨c,rfl⟩)|⟨b,rfl⟩
    · exact ⟨PresentedGroup.of (.A a),p.evaluate_generator hg _⟩
    · exact ⟨PresentedGroup.of (.D d),p.evaluate_generator hg _⟩
    · exact ⟨PresentedGroup.of (.C c),p.evaluate_generator hg _⟩
    · exact ⟨PresentedGroup.of (.B b),p.evaluate_generator hg _⟩
  · rintro x ⟨k,rfl⟩
    exact ⟨PresentedGroup.of (.torus k),p.evaluate_generator hg _⟩

/-- The constructed evaluation has exactly the expected matrix-generated image. -/
theorem evaluate_range {g : Generator RA RD RC RB H → M} (hg : p.Satisfies g) :
    (p.evaluate hg).range=ReflectionLaws.fullGenerated hg.roots hg.torus (g .s) (g .t) := by
  apply le_antisymm
  · rintro x ⟨z,rfl⟩
    let K := ReflectionLaws.fullGenerated hg.roots hg.torus (g .s) (g .t)
    have hz : z∈K.comap (p.evaluate hg) := by
      apply PresentedGroup.generated_by
      intro j
      change p.evaluate hg (PresentedGroup.of j)∈K
      rw [evaluate_generator]
      cases j with
      | A a => exact Subgroup.subset_closure (Or.inl (hg.roots.A_mem_borel _ a))
      | D d => exact Subgroup.subset_closure (Or.inl (hg.roots.D_mem_borel _ d))
      | C c => exact Subgroup.subset_closure (Or.inl (hg.roots.C_mem_borel _ c))
      | B b => exact Subgroup.subset_closure (Or.inl (hg.roots.B_mem_borel _ b))
      | torus k => exact Subgroup.subset_closure (Or.inl (hg.roots.torus_mem_borel _ k))
      | s => exact Subgroup.subset_closure (Or.inr (Or.inl rfl))
      | t => exact Subgroup.subset_closure (Or.inr (Or.inr rfl))
    exact hz
  · apply (Subgroup.closure_le _).mpr
    intro x hx
    rcases hx with hx|hx
    · exact p.borel_le_range hg hx
    · rcases hx with rfl|⟨rfl⟩
      · exact ⟨PresentedGroup.of .s,p.evaluate_generator hg _⟩
      · exact ⟨PresentedGroup.of .t,p.evaluate_generator hg _⟩

/-- Generation supplies surjectivity without any model-recognition input. -/
theorem evaluate_surjective {g : Generator RA RD RC RB H → M} (hg : p.Satisfies g)
    (hgen : ReflectionLaws.fullGenerated hg.roots hg.torus (g .s) (g .t)=⊤) :
    Function.Surjective (p.evaluate hg) :=
  MonoidHom.range_eq_top.mp ((p.evaluate_range hg).trans hgen)

end Parameters
end Presentation
end Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
