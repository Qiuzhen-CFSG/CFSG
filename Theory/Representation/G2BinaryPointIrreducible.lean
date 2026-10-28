module
public import Theory.Representation.G2BinaryPointFlag
/-!
# The binary point line and its irreducible seed quotient

The actual positive-root group fixes the first coordinate line. Its order
is two, while the marked seed has dimension three. The two literal point
actors E and R act irreducibly on the quotient: any vector outside the
point line yields the second basis vector, then its Weyl conjugate yields
the third. This supplies the point and irreducibility clauses in the
original F.9 applicability proof of Aschbacher–Smith 13.3.18(1), p.894.
-/

public section
namespace Atlas.G2.Natural.BinaryPointFlag
open Atlas.G2.Restricted.NaturalCoordinates Atlas.G2.Explicit Subgroup

def pointLine : Submodule F W := Submodule.span F {Pi.single 0 1}

theorem mem_pointLine (v:W) : v∈pointLine ↔ ∀i:Fin 6,i≠0→v i=0 := by
  constructor
  · intro hv
    obtain ⟨a,rfl⟩:=Submodule.mem_span_singleton.mp hv
    intro i hi
    simp [Ne.symm hi]
  · intro hv
    apply Submodule.mem_span_singleton.mpr
    refine ⟨v 0,?_⟩
    ext i
    by_cases hi:i=0
    · subst i;simp
    · simp [Ne.symm hi,hv i hi]

theorem pointLine_le_seed : pointLine≤seed := by
  intro v hv
  have hh:∀i:Fin 6,i≠0→v i=0 := (mem_pointLine v).mp hv
  exact (mem_seed v).mpr ⟨hh 3 (by decide),hh 4 (by decide),hh 5 (by decide)⟩

private def pointLineEquiv : pointLine≃F where
  toFun v:=v.val 0
  invFun a:=⟨a•Pi.single 0 1,Submodule.mem_span_singleton.mpr ⟨a,rfl⟩⟩
  left_inv v:=by
    apply Subtype.ext
    have hv:∀i:Fin 6,i≠0→v.val i=0:=(mem_pointLine v.val).mp v.prop
    ext i
    by_cases hi:i=0
    · subst i;simp
    · simp [Ne.symm hi,hv i hi]
  right_inv a:=by simp

theorem card_pointLine : Nat.card pointLine=2 := by
  rw [Nat.card_congr pointLineEquiv]
  simp

theorem pointLine_lt_seed : pointLine<seed := by
  apply lt_of_le_of_ne pointLine_le_seed
  intro he
  have hh:Pi.single (1:Fin 6) (1:F)∈pointLine:=he.symm ▸ (by simp:Pi.single (1:Fin 6) (1:F)∈seed)
  have hbad:=(mem_pointLine (Pi.single (1:Fin 6) (1:F):W)).mp hh 1 (by decide)
  simp at hbad

/-- The actual positive-root group fixes the original point line pointwise. -/
theorem unipotent_fixes_pointLine (g:Model F) (hg:g∈unipotent)
    (v:W) (hv:v∈pointLine) : Restricted.NaturalCoordinates.action F g v=v := by
  obtain ⟨a,rfl⟩:=Submodule.mem_span_singleton.mp hv
  rw [unipotent_eq_range] at hg
  obtain ⟨t,rfl⟩:=hg
  have hh:Restricted.NaturalCoordinates.action F (unipotentProduct t) (Pi.single 0 1)=Pi.single 0 1 := by
    ext i;fin_cases i <;>simp [unipotentProduct,map_mul,Module.End.mul_apply]
  rw [map_smul,hh]

/-- The actual E and R point actors act irreducibly on the marked
three-space modulo its first coordinate line. -/
theorem seed_point_invariant_interval (S:Submodule F W)
    (hline:pointLine≤S) (hseed:S≤seed)
    (hE:∀v∈S,Restricted.NaturalCoordinates.action F (rootE 1) v∈S)
    (hR:∀v∈S,Restricted.NaturalCoordinates.action F weylR v∈S) :
    S=pointLine ∨ S=seed := by
  by_cases heq:S≤pointLine
  · exact Or.inl (le_antisymm heq hline)
  right
  have h0:Pi.single (0:Fin 6) (1:F)∈S:=hline (Submodule.subset_span (by simp))
  obtain ⟨w,hw,hn⟩:=SetLike.not_le_iff_exists.mp heq
  obtain ⟨w3,w4,w5⟩:=(mem_seed w).mp (hseed hw)
  have hn':w 1≠0 ∨ w 2≠0 := by
    by_contra hh
    push Not at hh
    apply hn
    rw [mem_pointLine]
    intro i hi
    fin_cases i <;> simp_all
  have finish (v:W) (hv:v∈S) (he:v=w 0•Pi.single 0 1+Pi.single 1 1) :
      Pi.single (1:Fin 6) (1:F)∈S := by
    have hh:v-w 0•Pi.single 0 1=Pi.single 1 1:=by rw [he,add_sub_cancel_left]
    exact hh ▸ S.sub_mem hv (S.smul_mem _ h0)
  have h1:Pi.single (1:Fin 6) (1:F)∈S := by
    by_cases ha:w 1=0
    · have hb:w 2=1:=((by decide +kernel:∀x:F,x=0∨x=1) _).resolve_left
        (hn'.resolve_left (not_not_intro ha))
      apply finish _ (hR w hw)
      ext i;fin_cases i <;>simp [ha,hb,w3,w4,w5]
    · have ha':w 1=1:=((by decide +kernel:∀x:F,x=0∨x=1) _).resolve_left ha
      rcases (by decide +kernel:∀x:F,x=0∨x=1) (w 2) with hb|hb
      · apply finish w hw
        ext i;fin_cases i <;>simp [ha',hb,w3,w4,w5]
      · apply finish _ (hR _ (hE w hw))
        have h11:(1:F)+1=0:=by decide
        ext i;fin_cases i <;>simp [ha',hb,w3,w4,w5,h11]
  have h2:Pi.single (2:Fin 6) (1:F)∈S := by
    have he:Restricted.NaturalCoordinates.action F weylR (Pi.single 1 1)=Pi.single 2 1 := by
      ext i;fin_cases i <;>simp
    exact he ▸ hR _ h1
  apply le_antisymm hseed
  intro v hv
  obtain ⟨h3,h4,h5⟩:=(mem_seed v).mp hv
  have he:v=v 0•Pi.single 0 1+v 1•Pi.single 1 1+v 2•Pi.single 2 1 := by
    ext i;fin_cases i <;>simp [h3,h4,h5]
  rw [he]
  exact S.add_mem (S.add_mem (S.smul_mem _ h0) (S.smul_mem _ h1)) (S.smul_mem _ h2)
end Atlas.G2.Natural.BinaryPointFlag
