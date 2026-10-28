module

public import Theory.Combinatorics.SimpleGraph.QuadrangleTwentySeven.Local
public import Theory.Combinatorics.SimpleGraph.QuadrangleTwentySeven.Words

/-!
# Even-word coordinates for the 27-point quadrangle

The local flip operation reaches all sixteen even words. Since there are
exactly sixteen nonneighbors, their labels are bijective. Adjacency among
nonneighbors is precisely a four-coordinate flip. These facts supply the
structural coordinatization needed for the F.4.24 recognition.
-/

public section

open SimpleGraph
namespace Theory.Combinatorics.QuadrangleTwentySeven.Frame
variable {V:Type*} [Fintype V] {Γ:SimpleGraph V} [DecidableRel Γ.Adj]
 {x y:V} (D:Frame (Γ:=Γ) x y) (h:Γ.IsSRGWith 27 10 1 5) (hy:Γᶜ.Adj x y)
include D h hy

theorem exists_label (w:EvenWord) : ∃z:Far Γ x,D.label h z=w.val := by
  rcases even_cases w.val w.property with hz|⟨i,hi⟩|⟨i,j,_,hij⟩
  · exact ⟨⟨y,hy⟩,(D.label_base h hy).trans hz.symm⟩
  · obtain ⟨z,_,hz⟩:=D.exists_flip_neighbor h ⟨y,hy⟩ i
    refine ⟨z,?_⟩
    change D.label h z=flip i (D.label h ⟨y,hy⟩) at hz
    rw [D.label_base h hy] at hz
    exact hz.trans hi.symm
  · obtain ⟨z,_,hz⟩:=D.exists_flip_neighbor h ⟨y,hy⟩ j
    obtain ⟨u,_,hu⟩:=D.exists_flip_neighbor h z i
    change D.label h z=flip j (D.label h ⟨y,hy⟩) at hz
    change D.label h u=flip i (D.label h z) at hu
    rw [D.label_base h hy] at hz
    rw [hz] at hu
    exact ⟨u,hu.trans hij.symm⟩

private theorem bijective_section : ∃s:EvenWord→Far Γ x,
    Function.Bijective s ∧∀w,D.label h (s w)=w.val := by
  classical
  let s:EvenWord→Far Γ x:=fun w=>Classical.choose (D.exists_label h hy w)
  have hs (w:EvenWord) : D.label h (s w)=w.val := Classical.choose_spec (D.exists_label h hy w)
  have hi:Function.Injective s := by
    intro a b hab
    apply Subtype.ext
    exact (hs a).symm.trans ((congrArg (D.label h) hab).trans (hs b))
  exact ⟨s,(Fintype.bijective_iff_injective_and_card s).mpr
    ⟨hi,by rw [even_card,far_card h]⟩,hs⟩

theorem label_even (z:Far Γ x) : EvenWordPred (D.label h z) := by
  obtain ⟨s,hs,he⟩:=D.bijective_section h hy
  obtain ⟨w,rfl⟩:=hs.2 z
  rw [he]
  exact w.property

theorem label_injective : Function.Injective (D.label h) := by
  obtain ⟨s,hs,he⟩:=D.bijective_section h hy
  intro a b hab
  obtain ⟨v,rfl⟩:=hs.2 a
  obtain ⟨w,rfl⟩:=hs.2 b
  have hvw:v=w := Subtype.ext (by rwa [he,he] at hab)
  exact congrArg s hvw

@[expose] noncomputable def labelEquiv : Far Γ x≃EvenWord :=
  Equiv.ofBijective (fun z=>⟨D.label h z,D.label_even h hy z⟩)
    ⟨fun _ _ hh=>D.label_injective h hy (congrArg Subtype.val hh),fun w=>by
      obtain ⟨z,hz⟩:=D.exists_label h hy w
      exact ⟨z,Subtype.ext hz⟩⟩

@[simp] theorem labelEquiv_apply (z:Far Γ x) : (D.labelEquiv h hy z).val=D.label h z := rfl

@[simp] theorem labelEquiv_symm_apply (w:EvenWord) :
    D.label h ((D.labelEquiv h hy).symm w)=w.val := by
  exact congrArg Subtype.val ((D.labelEquiv h hy).apply_symm_apply w)

theorem adj_far_iff (z w:Far Γ x) : Γ.Adj z.val w.val ↔∃i,D.label h w=flip i (D.label h z) := by
  constructor
  · intro ha
    obtain ⟨i,hi⟩:=even_has_equal_coordinate (D.label h z) (D.label h w)
      (D.label_even h hy z) (D.label_even h hy w)
    refine ⟨i,?_⟩
    funext j
    by_cases hj:j=i
    · subst j
      simpa [flip] using hi.symm
    · rw [flip,if_neg hj]
      have hn:D.label h w j≠D.label h z j := by
        intro heq
        have he:=common_unique h ha (D.label_adj h z i)
          (by rw [hi];exact D.label_adj h w i) (D.label_adj h z j)
          (by rw [←heq];exact D.label_adj h w j)
        have hp:(i,D.label h z i)=(j,D.label h z j):=D.point_injective he
        exact hj (congrArg Prod.fst hp).symm
      cases hw:D.label h w j <;> cases hz:D.label h z j <;> simp_all
  · rintro ⟨i,hi⟩
    obtain ⟨q,hq,hql⟩:=D.exists_flip_neighbor h z i
    change D.label h q=flip i (D.label h z) at hql
    have he:w=q:=D.label_injective h hy (hi.trans hql.symm)
    exact he.symm ▸ hq

theorem far_eq_of_near_pattern (z w:Far Γ x)
    (he:∀a:Near Γ x,Γ.Adj z.val a.val↔Γ.Adj w.val a.val) : z=w := by
  apply D.label_injective h hy
  funext i
  exact (D.label_eq_of_adj h w i (D.label h z i)
    ((he (D.equiv (i,D.label h z i))).mp (D.label_adj h z i))).symm
end Theory.Combinatorics.QuadrangleTwentySeven.Frame
