module
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.Collection
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.Matrices
public import Theory.SpecificGroups.ClassicalUnitary.SmallCompletion.FiveRoots
public import BenderSuzuki.External.Huppert.II.theorem_10_12
public import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# The positive relative BC₂ roots in the actual special unitary five-space

The two multipliable root parameters are the full Hermitian groups, not
additive copies of the matrix field. A single explicit basis permutation
changes the existing (e₁,e₂,o,f₁,f₂) coordinates to (e₁,e₂,o,f₂,f₁).
All products below use this same permutation and the existing identity-form
SU₅ carrier. No field order or specialization to q=4 is imposed.

Source: Steinberg, Lectures on Chevalley Groups, Theorem 33 and Lemmas 63–64.
These are positive-root presentation inputs, not whole-group recognition.
-/

@[expose] public noncomputable section
open Matrix Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.External
namespace Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.FivePositive
open Theory.SpecificGroups.UnitaryFive
open PlaneCore SmallCompletion FivePaths FiveRoots
variable {E : Type*} [Field E] [CharP E 2]
variable (J : HermitianForm 5 E) (κ : E) (hκ : κ+J.conj κ=1) (hJ : J.form=1)

/-- The full Hermitian root group, with its inherited nonabelian multiplication. -/
abbrev Parameter := hermitianUnipotentCoord J

theorem parameter_relation (p : Parameter J) :
    p.val.2+J.conj p.val.2=p.val.1*J.conj p.val.1 :=
  (eq_neg_of_add_eq_zero_left p.property).trans (CharTwo.neg_eq _)

/-- Switch only the two final hyperbolic coordinates. -/
def orderSwap : Equiv.Perm (Fin 5) := Equiv.swap 3 4

/-- The same model matrices, expressed in the antidiagonal presentation basis. -/
def evaluate : J.specialSubgroup →* Matrix (Fin 5) (Fin 5) E :=
  (Matrix.reindexRingEquiv E orderSwap).toMonoidHom.comp
    ((Units.coeHom _).comp (coordinates J κ))

theorem evaluate_injective : Function.Injective (evaluate J κ) :=
  (Matrix.reindexRingEquiv E orderSwap).injective.comp
    (Units.val_injective.comp (coordinates_injective J κ))

def A (a : E) : J.specialSubgroup := linearRoot J κ hκ hJ a
def B (p : Parameter J) : J.specialSubgroup :=
  hermitianRoot J hJ p.val.1 p.val.2 (parameter_relation J p)

def cParameter (c : E) : Parameters J :=
  ⟨![0,0],!![0,c;J.conj c,0],by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [CharTwo.add_self_eq_zero]⟩

def dParameter (p : Parameter J) : Parameters J :=
  ⟨![p.val.1,0],!![p.val.2,0;0,0],by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [parameter_relation J p]⟩

def C (c : E) : J.specialSubgroup := Parameters.toSU hJ (cParameter J c)
def D (p : Parameter J) : J.specialSubgroup := Parameters.toSU hJ (dParameter J p)

theorem evaluate_A (a : E) : evaluate J κ (A J κ hκ hJ a)=Matrix5.A J.conj a := by
  change Matrix.reindexRingEquiv E orderSwap ((coordinates J κ (linearRoot J κ hκ hJ a)).val)=_
  rw [linearRoot_coordinates]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.reindexRingEquiv,Matrix.reindex,orderSwap,Equiv.swap_apply_def,Matrix5.A]

theorem evaluate_B (p : Parameter J) :
    evaluate J κ (B J hJ p)=Matrix5.B J.conj p.val.1 p.val.2 := by
  change Matrix.reindexRingEquiv E orderSwap ((coordinates J κ (hermitianRoot J hJ _ _ _)).val)=_
  rw [hermitianRoot_coordinates]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.reindexRingEquiv,Matrix.reindex,orderSwap,Equiv.swap_apply_def,Matrix5.B]

theorem evaluate_C (c : E) : evaluate J κ (C J hJ c)=Matrix5.C J.conj c := by
  change Matrix.reindexRingEquiv E orderSwap ((coordinates J κ (Parameters.toSU hJ _)).val)=_
  rw [coordinates_parameters]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.reindexRingEquiv,Matrix.reindex,orderSwap,Equiv.swap_apply_def,
      cParameter,Parameters.matrix,Matrix5.C]

theorem evaluate_D (p : Parameter J) :
    evaluate J κ (D J hJ p)=Matrix5.D J.conj p.val.1 p.val.2 := by
  change Matrix.reindexRingEquiv E orderSwap ((coordinates J κ (Parameters.toSU hJ _)).val)=_
  rw [coordinates_parameters]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.reindexRingEquiv,Matrix.reindex,orderSwap,Equiv.swap_apply_def,
      dParameter,Parameters.matrix,Matrix5.D]

def aHom : Multiplicative E →* J.specialSubgroup where
  toFun a := A J κ hκ hJ a.toAdd
  map_one' := by
    apply evaluate_injective J κ
    rw [(evaluate J κ).map_one,evaluate_A]
    change Matrix5.A J.conj 0=1
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix5.A]
  map_mul' a b := by
    apply evaluate_injective J κ
    rw [(evaluate J κ).map_mul,evaluate_A,evaluate_A,evaluate_A,Matrix5.A_mul]
    rfl

def bHom : Parameter J →* J.specialSubgroup where
  toFun := B J hJ
  map_one' := by
    apply evaluate_injective J (0:E)
    rw [map_one,evaluate_B]
    change Matrix5.B J.conj 0 0=1
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix5.B]
  map_mul' p q := by
    apply evaluate_injective J (0:E)
    rw [map_mul,evaluate_B,evaluate_B,evaluate_B,Matrix5.B_mul]
    change Matrix5.B J.conj (p.val.1+q.val.1) (p.val.2+q.val.2-p.val.1*J.conj q.val.1)=_
    rw [CharTwo.sub_eq_add]

def cHom : Multiplicative E →* J.specialSubgroup where
  toFun c := C J hJ c.toAdd
  map_one' := by
    apply evaluate_injective J (0:E)
    rw [(evaluate J (0:E)).map_one,evaluate_C]
    change Matrix5.C J.conj 0=1
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix5.C]
  map_mul' a b := by
    apply evaluate_injective J (0:E)
    rw [(evaluate J (0:E)).map_mul,evaluate_C,evaluate_C,evaluate_C,Matrix5.C_mul]
    rfl

def dHom : Parameter J →* J.specialSubgroup where
  toFun := D J hJ
  map_one' := by
    apply evaluate_injective J (0:E)
    rw [map_one,evaluate_D]
    change Matrix5.D J.conj 0 0=1
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix5.D]
  map_mul' p q := by
    apply evaluate_injective J (0:E)
    rw [map_mul,evaluate_D,evaluate_D,evaluate_D,Matrix5.D_mul]
    change Matrix5.D J.conj (p.val.1+q.val.1) (p.val.2+q.val.2-p.val.1*J.conj q.val.1)=_
    rw [CharTwo.sub_eq_add]

/-- The central Hermitian parameter in the short-short crossing. -/
def traceParameter (a c : E) : Parameter J := ⟨(0,a*J.conj c+J.conj a*c),by
  change (a*J.conj c+J.conj a*c)+J.conj (a*J.conj c+J.conj a*c)+0*J.conj 0=0
  simp only [map_add,map_mul,J.conj_involutive a,J.conj_involutive c,zero_mul,add_zero]
  ring_nf
  simp [CharTwo.two_eq_zero]⟩

/-- The full, generally noncentral Hermitian parameter in B(p)A(a). -/
def normParameter (a : E) (p : Parameter J) : Parameter J :=
  ⟨(a*p.val.1,a*J.conj a*p.val.2),by
    change (a*J.conj a*p.val.2)+J.conj (a*J.conj a*p.val.2)+
      (a*p.val.1)*J.conj (a*p.val.1)=0
    simp only [map_mul,J.conj_involutive a]
    linear_combination a*J.conj a*p.property⟩

theorem A_D (a : E) (p : Parameter J) : Commute (A J κ hκ hJ a) (D J hJ p) := by
  apply evaluate_injective J κ
  rw [map_mul,map_mul,evaluate_A,evaluate_D]
  exact Matrix5.A_D J.conj _ _ _

include κ in
theorem C_D (c : E) (p : Parameter J) : Commute (C J hJ c) (D J hJ p) := by
  apply evaluate_injective J κ
  rw [map_mul,map_mul,evaluate_C,evaluate_D]
  exact Matrix5.C_D J.conj _ _ _

include κ in
theorem B_C (p : Parameter J) (c : E) : Commute (B J hJ p) (C J hJ c) := by
  apply evaluate_injective J κ
  rw [map_mul,map_mul,evaluate_B,evaluate_C]
  exact Matrix5.B_C J.conj _ _ _

theorem C_A (a c : E) : C J hJ c * A J κ hκ hJ a =
    A J κ hκ hJ a * D J hJ (traceParameter J a c) * C J hJ c := by
  apply evaluate_injective J κ
  simp only [map_mul,evaluate_A,evaluate_C,evaluate_D]
  exact Matrix5.C_A J.conj a c

include κ in
theorem B_D (p q : Parameter J) : B J hJ p * D J hJ q =
    D J hJ q * C J hJ (q.val.1*J.conj p.val.1) * B J hJ p := by
  apply evaluate_injective J κ
  simp only [map_mul,evaluate_B,evaluate_C,evaluate_D]
  exact Matrix5.B_D J.conj J.conj_involutive _ _ _ _

theorem B_A (a : E) (p : Parameter J) : B J hJ p * A J κ hκ hJ a =
    A J κ hκ hJ a * D J hJ (normParameter J a p) *
      C J hJ (a*J.conj p.val.2) * B J hJ p := by
  apply evaluate_injective J κ
  simp only [map_mul,evaluate_A,evaluate_B,evaluate_C,evaluate_D]
  exact Matrix5.B_A J.conj J.conj_involutive _ _ _ (parameter_relation J p)

/-- The same four-root interface, with Hermitian rather than additive B,D. -/
def roots : PositiveMaps J.specialSubgroup (Multiplicative E) (Parameter J)
    (Multiplicative E) (Parameter J) :=
  ⟨aHom J κ hκ hJ,dHom J hJ,cHom J hJ,bHom J hJ⟩

theorem collects : (roots J κ hκ hJ).Collects where
  AD a p := A_D J κ hκ hJ a.toAdd p
  CD c p := C_D J κ hJ c.toAdd p
  BC p c := B_C J κ hJ p c.toAdd
  CA c a := ⟨traceParameter J a.toAdd c.toAdd,C_A J κ hκ hJ _ _⟩
  BD p q := ⟨Multiplicative.ofAdd (q.val.1*J.conj p.val.1),B_D J κ hJ p q⟩
  BA p a := ⟨normParameter J a.toAdd p,Multiplicative.ofAdd (a.toAdd*J.conj p.val.2),
    B_A J κ hκ hJ _ _⟩


/-- Positive words retain the two complete Hermitian parameters. -/
def word (p : E × Parameter J × E × Parameter J) : J.specialSubgroup :=
  A J κ hκ hJ p.1 * D J hJ p.2.1 * C J hJ p.2.2.1 * B J hJ p.2.2.2

theorem word_injective : Function.Injective (word J κ hκ hJ) := by
  rintro ⟨a,d,c,b⟩ ⟨a',d',c',b'⟩ he
  have hm := congrArg (evaluate J κ) he
  change evaluate J κ (A J κ hκ hJ a*D J hJ d*C J hJ c*B J hJ b)=
    evaluate J κ (A J κ hκ hJ a'*D J hJ d'*C J hJ c'*B J hJ b') at hm
  simp only [map_mul,evaluate_A,evaluate_D,evaluate_C,evaluate_B] at hm
  have hp : (a,d.val,c,b.val)=(a',d'.val,c',b'.val) := Matrix5.word_injective J.conj hm
  have ha := congrArg Prod.fst hp
  have hd : d=d' := Subtype.ext (congrArg (fun p : E × (E × E) × E × (E × E) => p.2.1) hp)
  have hc := congrArg (fun p : E × (E × E) × E × (E × E) => p.2.2.1) hp
  have hb : b=b' := Subtype.ext (congrArg (fun p : E × (E × E) × E × (E × E) => p.2.2.2) hp)
  cases ha; cases hd; cases hc; cases hb
  rfl

/-- Both Hermitian constraints, rather than eight additive coordinates, are
retained in the unique positive word on the actual SU₅ model. -/
theorem generated_existsUnique_word (g : J.specialSubgroup)
    (hg : g∈(roots J κ hκ hJ).generated) :
    ∃! p : E × Parameter J × E × Parameter J, word J κ hκ hJ p=g := by
  obtain ⟨a,d,c,b,he⟩ := PositiveMaps.exists_word (collects J κ hκ hJ) hg
  refine ⟨(a.toAdd,d,c.toAdd,b),he.symm,?_⟩
  intro q hq
  exact word_injective J κ hκ hJ (hq.trans he)

/-- A diagonal entry of the plane radical gives a full Hermitian parameter. -/
def diagonalParameter (u : Parameters J) (i : Fin 2) : Parameter J :=
  ⟨(u.x i,u.z i i),by
    change u.z i i+J.conj (u.z i i)+u.x i*J.conj (u.x i)=0
    rw [u.relation,CharTwo.add_self_eq_zero]⟩

include κ in
/-- The existing full plane radical is the D,C,B product in this convention. -/
theorem plane_radical_word (u : Parameters J) :
    Parameters.toSU hJ u = D J hJ (diagonalParameter J u 0) *
      C J hJ (J.conj (u.z 1 0)) * B J hJ (diagonalParameter J u 1) := by
  apply evaluate_injective J κ
  rw [map_mul,map_mul,evaluate_D,evaluate_C,evaluate_B,Matrix5.D_C_B]
  change Matrix.reindexRingEquiv E orderSwap ((coordinates J κ (Parameters.toSU hJ u)).val)=_
  rw [coordinates_parameters]
  have h01 : u.z 0 1=u.x 0*J.conj (u.x 1)+J.conj (u.z 1 0) := by
    have h := congrArg (fun z : E => z+J.conj (u.z 1 0)) (u.relation 0 1)
    simpa [add_assoc,CharTwo.add_self_eq_zero] using h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.reindexRingEquiv,Matrix.reindex,orderSwap,Equiv.swap_apply_def,
      Parameters.matrix,diagonalParameter,J.conj_involutive (u.z 1 0),h01]

/-- The concrete plane-radical consumer needs no extra generator or q=4 hypothesis. -/
theorem plane_radical_mem_generated (u : Parameters J) :
    Parameters.toSU hJ u∈(roots J κ hκ hJ).generated := by
  have hm := (roots J κ hκ hJ).word_mem 1 (diagonalParameter J u 0)
    (Multiplicative.ofAdd (J.conj (u.z 1 0))) (diagonalParameter J u 1)
  change aHom J κ hκ hJ 1 * D J hJ _ * C J hJ _ * B J hJ _∈_ at hm
  rw [map_one,one_mul] at hm
  rwa [plane_radical_word J κ hJ u]


/-- Exact positive BC₂ equations, including the nontrivial B,D crossing. -/
structure Relations {G : Type*} [Group G]
    (r : PositiveMaps G (Multiplicative E) (Parameter J) (Multiplicative E) (Parameter J)) : Prop where
  AD : ∀ a d, Commute (r.A a) (r.D d)
  CD : ∀ c d, Commute (r.C c) (r.D d)
  BC : ∀ b c, Commute (r.B b) (r.C c)
  CA : ∀ a c, r.C (Multiplicative.ofAdd c)*r.A (Multiplicative.ofAdd a) =
    r.A (Multiplicative.ofAdd a)*r.D (traceParameter J a c)*r.C (Multiplicative.ofAdd c)
  BD : ∀ p q, r.B p*r.D q = r.D q*r.C (Multiplicative.ofAdd (q.val.1*J.conj p.val.1))*r.B p
  BA : ∀ a p, r.B p*r.A (Multiplicative.ofAdd a) =
    r.A (Multiplicative.ofAdd a)*r.D (normParameter J a p)*
      r.C (Multiplicative.ofAdd (a*J.conj p.val.2))*r.B p

/-- The exact Hermitian equations suffice for abstract positive collection. -/
theorem Relations.collects {G : Type*} [Group G]
    {r : PositiveMaps G (Multiplicative E) (Parameter J) (Multiplicative E) (Parameter J)}
    (h : Relations J r) : r.Collects where
  AD := h.AD
  CD := h.CD
  BC := h.BC
  CA c a := ⟨traceParameter J a.toAdd c.toAdd,h.CA _ _⟩
  BD p q := ⟨Multiplicative.ofAdd (q.val.1*J.conj p.val.1),h.BD p q⟩
  BA p a := ⟨normParameter J a.toAdd p,Multiplicative.ofAdd (a.toAdd*J.conj p.val.2),h.BA _ _⟩

/-- All the Hermitian equations hold in the actual SU₅ model, for every field. -/
theorem model_relations : Relations J (roots J κ hκ hJ) where
  AD := (collects J κ hκ hJ).AD
  CD := (collects J κ hκ hJ).CD
  BC := (collects J κ hκ hJ).BC
  CA := C_A J κ hκ hJ
  BD := B_D J κ hJ
  BA := B_A J κ hκ hJ

end Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.FivePositive
