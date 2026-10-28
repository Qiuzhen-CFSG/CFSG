module
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.Collection
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.Matrices
public import Theory.SpecificGroups.ClassicalUnitary.SmallCompletion.FourRoots

/-!
# The four positive roots in the actual special unitary four-space

The linear roots have parameters in E; the two long roots have parameters
in the actual fixed field. The coordinate a in A is the conjugate of the
existing `FourRoots.shortRoot` parameter. All six crossing laws and unique
ordered coordinates are proved in the actual SU carrier.

Source: Steinberg, Lectures on Chevalley Groups, Theorem 33 and Lemma 64.
This supplies the positive subgroup for the new relative Bruhat presentation.
-/

@[expose] public noncomputable section
open Matrix Subgroup BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.FourPositive
open UnitaryFourFlag UnitaryFourPointLocal UnitaryFourPointQuotient UnitaryFourSylow
open SmallCompletion
variable (E : Type*) [Field E] [CharP E 2]
variable (σ : E ≃+* E) (hσ : Function.Involutive σ)
local notation "J" => form E σ hσ
local notation "K" => FixedField E σ

def A (a : E) : SU E J := FourRoots.shortRoot E σ hσ (σ a)
def B (b : K) : SU E J := FourRoots.longRoot E σ hσ b
def C (c : E) : SU E J := radicalElement E σ hσ ⟨σ c,0,0,by simp⟩
def D (d : K) : SU E J := radicalElement E σ hσ ⟨0,0,d,by
  have hd : σ (d:E)=(d:E) := d.property
  simp [hd,CharTwo.add_self_eq_zero]⟩

theorem A_val (a : E) : (A E σ hσ a).val.val=Matrix4.A σ a := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [A,FourRoots.shortRoot,radicalElement,radicalMatrix,Matrix4.A,hσ a]

theorem B_val (b : K) : (B E σ hσ b).val.val=Matrix4.B (b:E) := by
  change (leviSL E σ hσ _).val.val.val=_
  rw [leviSL_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [leviMatrix,SpecialLinearGroup.upperUnipotentHom,SpecialLinearGroup.transvection_coe,Matrix4.B]

theorem C_val (c : E) : (C E σ hσ c).val.val=Matrix4.C σ c := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [C,radicalElement,radicalMatrix,Matrix4.C,hσ c]

theorem D_val (d : K) : (D E σ hσ d).val.val=Matrix4.D (d:E) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [D,radicalElement,radicalMatrix,Matrix4.D]

def aHom : Multiplicative E →* SU E J where
  toFun a := A E σ hσ a.toAdd
  map_one' := by
    apply Subtype.ext; apply Units.ext
    change (A E σ hσ 0).val.val=1
    rw [A_val]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix4.A]
  map_mul' a b := by
    apply Subtype.ext; apply Units.ext
    change (A E σ hσ (a.toAdd+b.toAdd)).val.val=_
    rw [A_val]
    change _=(A E σ hσ a.toAdd).val.val*(A E σ hσ b.toAdd).val.val
    rw [A_val,A_val,Matrix4.A_mul]

def bHom : Multiplicative K →* SU E J where
  toFun b := B E σ hσ b.toAdd
  map_one' := by
    apply Subtype.ext; apply Units.ext
    change (B E σ hσ 0).val.val=1
    rw [B_val]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix4.B]
  map_mul' a b := by
    apply Subtype.ext; apply Units.ext
    change (B E σ hσ (a.toAdd+b.toAdd)).val.val=_
    rw [B_val]
    change _=(B E σ hσ a.toAdd).val.val*(B E σ hσ b.toAdd).val.val
    rw [B_val,B_val,Matrix4.B_mul]
    rfl

def cHom : Multiplicative E →* SU E J where
  toFun c := C E σ hσ c.toAdd
  map_one' := by
    apply Subtype.ext; apply Units.ext
    change (C E σ hσ 0).val.val=1
    rw [C_val]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix4.C]
  map_mul' a b := by
    apply Subtype.ext; apply Units.ext
    change (C E σ hσ (a.toAdd+b.toAdd)).val.val=_
    rw [C_val]
    change _=(C E σ hσ a.toAdd).val.val*(C E σ hσ b.toAdd).val.val
    rw [C_val,C_val,Matrix4.C_mul]

def dHom : Multiplicative K →* SU E J where
  toFun d := D E σ hσ d.toAdd
  map_one' := by
    apply Subtype.ext; apply Units.ext
    change (D E σ hσ 0).val.val=1
    rw [D_val]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix4.D]
  map_mul' a b := by
    apply Subtype.ext; apply Units.ext
    change (D E σ hσ (a.toAdd+b.toAdd)).val.val=_
    rw [D_val]
    change _=(D E σ hσ a.toAdd).val.val*(D E σ hσ b.toAdd).val.val
    rw [D_val,D_val,Matrix4.D_mul]
    rfl

/-- The short-short crossing parameter, in the actual fixed field. -/
def traceParameter (a c : E) : K := ⟨a*σ c+σ a*c,by
  change σ (a*σ c+σ a*c)=a*σ c+σ a*c
  simp [map_add,map_mul,hσ a,hσ c,add_comm]⟩

/-- The long correction in B(t)A(a). -/
def normParameter (a : E) (t : K) : K := ⟨a*σ a*(t:E),by
  have ht : σ (t:E)=(t:E) := t.property
  change σ (a*σ a*(t:E))=a*σ a*(t:E)
  simp [map_mul,hσ a,ht,mul_comm]⟩

theorem A_D (a : E) (d : K) : Commute (A E σ hσ a) (D E σ hσ d) := by
  apply Subtype.ext; apply Units.ext
  change (A E σ hσ a).val.val*(D E σ hσ d).val.val=(D E σ hσ d).val.val*(A E σ hσ a).val.val
  rw [A_val,D_val]
  exact Matrix4.A_D σ a d

theorem C_D (c : E) (d : K) : Commute (C E σ hσ c) (D E σ hσ d) := by
  apply Subtype.ext; apply Units.ext
  change (C E σ hσ c).val.val*(D E σ hσ d).val.val=(D E σ hσ d).val.val*(C E σ hσ c).val.val
  rw [C_val,D_val]
  exact Matrix4.C_D σ c d

theorem B_C (b : K) (c : E) : Commute (B E σ hσ b) (C E σ hσ c) := by
  apply Subtype.ext; apply Units.ext
  change (B E σ hσ b).val.val*(C E σ hσ c).val.val=(C E σ hσ c).val.val*(B E σ hσ b).val.val
  rw [B_val,C_val]
  exact Matrix4.B_C σ b c

theorem B_D (b d : K) : Commute (B E σ hσ b) (D E σ hσ d) := by
  apply Subtype.ext; apply Units.ext
  change (B E σ hσ b).val.val*(D E σ hσ d).val.val=(D E σ hσ d).val.val*(B E σ hσ b).val.val
  rw [B_val,D_val]
  exact Matrix4.B_D (b:E) (d:E)

theorem C_A (a c : E) : C E σ hσ c * A E σ hσ a =
    A E σ hσ a * D E σ hσ (traceParameter E σ hσ a c) * C E σ hσ c := by
  apply Subtype.ext; apply Units.ext
  change (C E σ hσ c).val.val*(A E σ hσ a).val.val=
    (A E σ hσ a).val.val*(D E σ hσ _).val.val*(C E σ hσ c).val.val
  rw [C_val,A_val,D_val]
  exact Matrix4.C_A σ a c

theorem B_A (a : E) (b : K) : B E σ hσ b * A E σ hσ a =
    A E σ hσ a * D E σ hσ (normParameter E σ hσ a b) *
      C E σ hσ (a*(b:E)) * B E σ hσ b := by
  apply Subtype.ext; apply Units.ext
  change (B E σ hσ b).val.val*(A E σ hσ a).val.val=
    (A E σ hσ a).val.val*(D E σ hσ _).val.val*(C E σ hσ _).val.val*(B E σ hσ b).val.val
  rw [B_val,A_val,D_val,C_val]
  exact Matrix4.B_A σ a b b.property

/-- The common collection interface instantiated by actual SU₄ matrices. -/
def roots : PositiveMaps (SU E J) (Multiplicative E) (Multiplicative K)
    (Multiplicative E) (Multiplicative K) :=
  ⟨aHom E σ hσ,dHom E σ hσ,cHom E σ hσ,bHom E σ hσ⟩

theorem collects : (roots E σ hσ).Collects where
  AD a d := A_D E σ hσ a.toAdd d.toAdd
  CD c d := C_D E σ hσ c.toAdd d.toAdd
  BC b c := B_C E σ hσ b.toAdd c.toAdd
  CA c a := ⟨Multiplicative.ofAdd (traceParameter E σ hσ a.toAdd c.toAdd), C_A E σ hσ _ _⟩
  BD b d := ⟨1,by
    change B E σ hσ b.toAdd * D E σ hσ d.toAdd =
      D E σ hσ d.toAdd * cHom E σ hσ 1 * B E σ hσ b.toAdd
    rw [map_one,mul_one]
    exact (B_D E σ hσ _ _).eq⟩
  BA b a := ⟨Multiplicative.ofAdd (normParameter E σ hσ a.toAdd b.toAdd),
    Multiplicative.ofAdd (a.toAdd*(b.toAdd:E)),B_A E σ hσ _ _⟩


/-- The ordinary field and fixed-field coordinates in positive-root order. -/
def word (p : E × K × E × K) : SU E J :=
  A E σ hσ p.1 * D E σ hσ p.2.1 * C E σ hσ p.2.2.1 * B E σ hσ p.2.2.2

theorem word_injective : Function.Injective (word E σ hσ) := by
  rintro ⟨a,d,c,b⟩ ⟨a',d',c',b'⟩ he
  have hm := congrArg (fun g : SU E J => g.val.val) he
  change (A E σ hσ a).val.val*(D E σ hσ d).val.val*(C E σ hσ c).val.val*(B E σ hσ b).val.val =
    (A E σ hσ a').val.val*(D E σ hσ d').val.val*(C E σ hσ c').val.val*(B E σ hσ b').val.val at hm
  simp only [A_val,D_val,C_val,B_val] at hm
  have hp : (a,(d:E),c,(b:E))=(a',(d':E),c',(b':E)) := Matrix4.word_injective σ hm
  have ha := congrArg Prod.fst hp
  have hd : d=d' := Subtype.ext (congrArg (fun p : E × E × E × E => p.2.1) hp)
  have hc := congrArg (fun p : E × E × E × E => p.2.2.1) hp
  have hb : b=b' := Subtype.ext (congrArg (fun p : E × E × E × E => p.2.2.2) hp)
  cases ha; cases hd; cases hc; cases hb
  rfl

private theorem radical_word (r : RadicalCoordinates E σ) :
    radicalElement E σ hσ r =
      A E σ hσ (σ r.y) * D E σ hσ ((radicalParametersEquiv E σ hσ r).2.2) *
        C E σ hσ (σ r.x) := by
  apply Subtype.ext; apply Units.ext
  change radicalMatrix E σ r =
    (A E σ hσ (σ r.y)).val.val*(D E σ hσ _).val.val*(C E σ hσ (σ r.x)).val.val
  rw [A_val,D_val,C_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [radicalMatrix,Matrix4.A,Matrix4.C,Matrix4.D,radicalParametersEquiv,
      Matrix.mul_apply,Fin.sum_univ_succ,hσ r.x,hσ r.y,add_left_comm,mul_comm,CharTwo.add_self_eq_zero]

/-- Collection covers the literal upper-unitriangular SU₄ subgroup. -/
theorem upper_exists_word (g : SU E J) (hg : g∈upper E σ hσ) :
    ∃ p : E × K × E × K, word E σ hσ p=g := by
  rcases hg with ⟨u,hu,rfl⟩
  obtain ⟨t,ht⟩ := (SpecialLinearGroup.mem_upperUnipotent K _).mp hu
  let v := leviSL E σ hσ (SpecialLinearGroup.upperUnipotentHom K (Multiplicative.ofAdd t))
  have hv : middleSL E σ hσ v=middleSL E σ hσ u := by
    rw [middleSL_leviSL]
    exact ht
  have hrad : u*v⁻¹∈radical E σ hσ := by
    rw [←middleSL_ker]
    change middleSL E σ hσ (u*v⁻¹)=1
    rw [map_mul,map_inv,hv,mul_inv_cancel]
  obtain ⟨r,hr⟩ := (radicalCoordinatesEquiv E σ hσ).surjective ⟨u*v⁻¹,hrad⟩
  have he : radicalElement E σ hσ r=u.val*v.val⁻¹ :=
    congrArg (fun r : radical E σ hσ => r.val.val) hr
  refine ⟨(σ r.y,(radicalParametersEquiv E σ hσ r).2.2,σ r.x,t),?_⟩
  change (A E σ hσ _*D E σ hσ _*C E σ hσ _)*v.val=u.val
  rw [←radical_word,he]
  exact inv_mul_cancel_right _ _

/-- The actual positive matrix subgroup has unique ordered coordinates. -/
theorem upper_existsUnique_word (g : SU E J) (hg : g∈upper E σ hσ) :
    ∃! p : E × K × E × K, word E σ hσ p=g := by
  obtain ⟨p,hp⟩ := upper_exists_word E σ hσ g hg
  exact ⟨p,hp,fun q hq => word_injective E σ hσ (hq.trans hp.symm)⟩

/-- The four maps generate precisely the existing upper-unitriangular subgroup. -/
theorem generated_eq_upper : (roots E σ hσ).generated=upper E σ hσ := by
  apply le_antisymm
  · apply (Subgroup.closure_le (upper E σ hσ)).mpr
    rintro g (((⟨a,rfl⟩ | ⟨d,rfl⟩) | ⟨c,rfl⟩) | ⟨b,rfl⟩)
    · exact FourRoots.shortRoot_mem_upper E σ hσ _
    · exact radicalElement_mem_upper E σ hσ _
    · exact radicalElement_mem_upper E σ hσ _
    · exact FourRoots.longRoot_mem_upper E σ hσ _
  · intro g hg
    obtain ⟨⟨a,d,c,b⟩,rfl⟩ := upper_exists_word E σ hσ g hg
    exact (roots E σ hσ).word_mem (Multiplicative.ofAdd a) (Multiplicative.ofAdd d)
      (Multiplicative.ofAdd c) (Multiplicative.ofAdd b)


/-- The exact four-dimensional positive equations, usable on another group.
The trace and norm parameters remain in the actual fixed subfield. -/
structure Relations {G : Type*} [Group G]
    (r : PositiveMaps G (Multiplicative E) (Multiplicative K) (Multiplicative E) (Multiplicative K)) : Prop where
  AD : ∀ a d, Commute (r.A a) (r.D d)
  CD : ∀ c d, Commute (r.C c) (r.D d)
  BC : ∀ b c, Commute (r.B b) (r.C c)
  BD : ∀ b d, Commute (r.B b) (r.D d)
  CA : ∀ a c, r.C (Multiplicative.ofAdd c)*r.A (Multiplicative.ofAdd a) =
    r.A (Multiplicative.ofAdd a)*r.D (Multiplicative.ofAdd (traceParameter E σ hσ a c))*r.C (Multiplicative.ofAdd c)
  BA : ∀ a b, r.B (Multiplicative.ofAdd b)*r.A (Multiplicative.ofAdd a) =
    r.A (Multiplicative.ofAdd a)*r.D (Multiplicative.ofAdd (normParameter E σ hσ a b))*
      r.C (Multiplicative.ofAdd (a*(b:E)))*r.B (Multiplicative.ofAdd b)

omit [CharP E 2] in
/-- Exact field equations imply collection in an arbitrary target group. -/
theorem Relations.collects {G : Type*} [Group G]
    {r : PositiveMaps G (Multiplicative E) (Multiplicative K) (Multiplicative E) (Multiplicative K)}
    (h : Relations E σ hσ r) : r.Collects where
  AD := h.AD
  CD := h.CD
  BC := h.BC
  CA c a := ⟨Multiplicative.ofAdd (traceParameter E σ hσ a.toAdd c.toAdd),h.CA _ _⟩
  BD b d := ⟨1,by simpa only [map_one,mul_one] using (h.BD b d).eq⟩
  BA b a := ⟨Multiplicative.ofAdd (normParameter E σ hσ a.toAdd b.toAdd),
    Multiplicative.ofAdd (a.toAdd*(b.toAdd:E)),h.BA _ _⟩

/-- All the field equations hold in the actual SU₄ model. -/
theorem model_relations : Relations E σ hσ (roots E σ hσ) where
  AD := (collects E σ hσ).AD
  CD := (collects E σ hσ).CD
  BC := (collects E σ hσ).BC
  BD b d := B_D E σ hσ b.toAdd d.toAdd
  CA := C_A E σ hσ
  BA := B_A E σ hσ

end Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.FourPositive
