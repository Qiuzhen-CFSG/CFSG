module
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.BorelCollection
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.RankOneCollection

/-!
# The two-cell step for the full generated Borel

Torus action first collects U H. The rank-one root equations and the Weyl
action on the torus then give s B s contained in B union B s B, and the
analogous point-reflection statement, entirely inside an arbitrary group.
Source: Steinberg, Lectures on Chevalley Groups, Lemmas 21–24.
-/
@[expose] public section
namespace Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
variable {G RA RD RC RB H : Type*} [Group G] [Group RA] [Group RD] [Group RC] [Group RB] [Group H]
namespace ReflectionLaws
variable {r : PositiveMaps G RA RD RC RB} {h : H →* G} {s t : G}

/-- The plane-reflection two-cell alternative for the entire root-and-torus subgroup. -/
theorem s_borel (e : ReflectionLaws r h s t) (hc : r.Collects) (ht : r.TorusLaws h)
    (hsh : ∀ k, ∃ l, s*h k*s=h l) {x : G} (hx : x∈r.borel h) :
    s*x*s∈r.borel h ∨ ∃ l∈r.borel h, ∃ v∈r.borel h, s*x*s=l*s*v := by
  obtain ⟨a,d,c,b,k,rfl⟩ := ht.exists_word hc hx
  obtain ⟨k',hk'⟩ := hsh k
  have hH : h k'∈r.borel h := (le_sup_right : h.range≤r.borel h) ⟨k',rfl⟩
  have hs (y : G) : s*(s*y)=y := by rw [←mul_assoc,e.ss,one_mul]
  have he : s*(r.word a d c b*h k)*s=(s*r.word a d c b*s)*h k' := by
    rw [←hk']
    simp only [mul_assoc,hs]
  rw [he]
  rcases e.s_word (r.borel h) le_sup_left le_sup_right a d c b with hm|⟨l,hl,v,hv,heq⟩
  · exact Or.inl ((r.borel h).mul_mem hm hH)
  · exact Or.inr ⟨l,hl,v*h k',(r.borel h).mul_mem hv hH,by rw [heq,mul_assoc]⟩

/-- The point-reflection two-cell alternative keeps the full Hermitian root. -/
theorem t_borel (e : ReflectionLaws r h s t) (hc : r.Collects) (ht : r.TorusLaws h)
    (hth : ∀ k, ∃ l, t*h k*t=h l) {x : G} (hx : x∈r.borel h) :
    t*x*t∈r.borel h ∨ ∃ l∈r.borel h, ∃ v∈r.borel h, t*x*t=l*t*v := by
  obtain ⟨a,d,c,b,k,rfl⟩ := ht.exists_word hc hx
  obtain ⟨k',hk'⟩ := hth k
  have hH : h k'∈r.borel h := (le_sup_right : h.range≤r.borel h) ⟨k',rfl⟩
  have hs (y : G) : t*(t*y)=y := by rw [←mul_assoc,e.tt,one_mul]
  have he : t*(r.word a d c b*h k)*t=(t*r.word a d c b*t)*h k' := by
    rw [←hk']
    simp only [mul_assoc,hs]
  rw [he]
  rcases e.t_word (r.borel h) le_sup_left le_sup_right a d c b with hm|⟨l,hl,v,hv,heq⟩
  · exact Or.inl ((r.borel h).mul_mem hm hH)
  · exact Or.inr ⟨l,hl,v*h k',(r.borel h).mul_mem hv hH,by rw [heq,mul_assoc]⟩

end ReflectionLaws
end Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
