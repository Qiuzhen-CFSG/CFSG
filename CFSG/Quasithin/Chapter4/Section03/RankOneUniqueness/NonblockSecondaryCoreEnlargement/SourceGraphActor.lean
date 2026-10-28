module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceFrameSylow
public import Theory.SpecificGroups.PSL3Even.MinimalParabolicWitness.Center
public import Theory.SpecificGroups.PSL3.OuterSolvable.StandardQuotient

/-!
# The graph component of the original crossing

The original crossing preserves the full inner Sylow image and moves the
radical root plane. In their common frame its diagram action is therefore
nontrivial. The diagram kernel is normal, so this remains true in the original
marking. Standard automorphism coverage gives the precise graph/field form;
no involution or trivial field part is assumed.
Source: Aschbacher–Smith, original 4.3.14–16 and B.4.14, pp.617–619,98.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Matrix
open scoped MatrixGroups
open Matrix.PSL3.LinearThree Matrix.PSL3.RootPlaneGeometry
open Matrix.PSL3.LinearThree.OuterExtensions
open Matrix.PSL3.OuterSolvable Matrix.PSL3.ExtensionBorel
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ}
namespace SecondaryActionData

private theorem congr_inner {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (x : A) :
    MulAut.congr e (MulAut.conj x) = MulAut.conj (e x) := by
  ext y
  simp [MulAut.congr_apply,MulAut.conj_apply]

omit [Finite G] in
/-- The original full marking identifies its literal component image with PSL₃,
with the inner embedding equation retained. -/
theorem exists_inner_marking (s : SecondaryActionData c n)
    {F : Type*} [Field F] [Finite F]
    (mark : (s.component ⧸ pCore 2 s.component) ≃* PSL(3,F)) :
    ∃ e : componentImage s ≃* PSL(3,F),
      (MulAut.conj : PSL(3,F) →* MulAut PSL(3,F)).comp e.toMonoidHom =
        (MulAut.congr mark).toMonoidHom.comp (componentImage s).subtype := by
  let j : PSL(3,F) →* componentImage s :=
    ((MulAut.conj : (s.component ⧸ pCore 2 s.component) →*
      MulAut (s.component ⧸ pCore 2 s.component)).comp mark.symm.toMonoidHom).codRestrict
      (componentImage s) (fun x => by
        rw [componentImage_eq_inner]
        exact ⟨mark.symm x,rfl⟩)
  have hj : Function.Injective j := by
    intro x y h
    apply inner_injective F
    have hh := congrArg (fun z : componentImage s => MulAut.congr mark z.val) h
    simp only [j,MonoidHom.codRestrict_apply,MonoidHom.comp_apply,
      MulEquiv.toMonoidHom_eq_coe,congr_inner] at hh
    simpa using hh
  have hs : Function.Surjective j := by
    intro x
    have hx := x.property
    have hx : x.val ∈ MulAut.innerSubgroup (s.component ⧸ pCore 2 s.component) :=
      (componentImage_eq_inner s) ▸ hx
    obtain ⟨y,hy⟩ := hx
    refine ⟨mark y,Subtype.ext ?_⟩
    change MulAut.conj (mark.symm (mark y)) = x.val
    rw [mark.symm_apply_apply]
    exact hy
  let k := MulEquiv.ofBijective j ⟨hj,hs⟩
  refine ⟨k.symm,?_⟩
  apply MonoidHom.ext
  intro x
  obtain ⟨y,rfl⟩ := k.surjective x
  change MulAut.conj (k.symm (k y)) = MulAut.congr mark (MulAut.conj (mark.symm y))
  rw [k.symm_apply_apply,congr_inner,mark.apply_symm_apply]

omit [Finite G] in
private theorem model_image_inner (s : SecondaryActionData c n)
    {F : Type*} [Field F] [Finite F]
    (mark : (s.component ⧸ pCore 2 s.component) ≃* PSL(3,F))
    (e : componentImage s ≃* PSL(3,F))
    (he : (MulAut.conj : PSL(3,F) →* MulAut PSL(3,F)).comp e.toMonoidHom =
      (MulAut.congr mark).toMonoidHom.comp (componentImage s).subtype)
    (H : Subgroup (MulAut (s.component ⧸ pCore 2 s.component))) (hH : H ≤ componentImage s) :
    (((H.subgroupOf (componentImage s)).map e.toMonoidHom).map MulAut.conj) =
      H.map (MulAut.congr mark).toMonoidHom := by
  rw [Subgroup.map_map,he,←Subgroup.map_map,map_subgroupOf_eq_of_le hH]

private theorem inner_map_actor {F : Type*} [Field F]
    (H : Subgroup PSL(3,F)) (a : MulAut PSL(3,F)) :
    (H.map a.toMonoidHom).map MulAut.conj =
      (H.map MulAut.conj).map (MulAut.conj a).toMonoidHom := by
  rw [Subgroup.map_map,Subgroup.map_map]
  congr 1
  ext x y
  simp [MulAut.conj_apply,map_mul,map_inv]

private theorem map_actor_congr {A B : Type*} [Group A] [Group B]
    (H : Subgroup A) (a : MulAut A) (e : A ≃* B) :
    (H.map a.toMonoidHom).map e.toMonoidHom =
      (H.map e.toMonoidHom).map (MulAut.congr e a).toMonoidHom := by
  rw [Subgroup.map_map,Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.congr_apply]

omit [Finite G] in
/--
The inner model image preserves a subgroup whenever the corresponding
automorphism preserves that subgroup in the original quotient.  This is the
transport interface used by the source cubic-frame consumer.
-/
theorem model_image_preserves (s : SecondaryActionData c n)
    {F : Type*} [Field F] [Finite F]
    (mark : (s.component ⧸ pCore 2 s.component) ≃* PSL(3,F))
    (e : componentImage s ≃* PSL(3,F))
    (he : (MulAut.conj : PSL(3,F) →* MulAut PSL(3,F)).comp e.toMonoidHom =
      (MulAut.congr mark).toMonoidHom.comp (componentImage s).subtype)
    (H : Subgroup (MulAut (s.component ⧸ pCore 2 s.component))) (hH : H ≤ componentImage s)
    (t : MulAut (s.component ⧸ pCore 2 s.component))
    (ht : H.map (MulAut.conj t).toMonoidHom = H) :
    ((H.subgroupOf (componentImage s)).map e.toMonoidHom).map
      ((MulAut.congr mark) t).toMonoidHom =
      (H.subgroupOf (componentImage s)).map e.toMonoidHom := by
  apply Subgroup.map_injective (inner_injective F)
  rw [inner_map_actor,model_image_inner s mark e he H hH]
  have hh := congrArg (Subgroup.map (MulAut.congr mark).toMonoidHom) ht
  rw [map_actor_congr,congr_inner] at hh
  exact hh

/-- A Sylow-preserving actor moving a root plane has nontrivial diagram action. -/
theorem not_linearField_of_root_plane_moved {F : Type*} [Field F] [Finite F] [CharP F 2]
    {f : ℕ} (hf : 0<f) (hF : Nat.card F = 2^f) (a : MulAut PSL(3,F))
    (hU : (unipotent F).map a.toMonoidHom = unipotent F)
    (b : Bool) (hR : (rootPlane F b).map a.toMonoidHom ≠ rootPlane F b) :
    a ∉ linearField F := by
  intro ha
  apply hR
  rw [Matrix.PSL3Even.MinimalParabolicWitness.map_rootPlane_of_preserves_unipotent
    F hf hF a hU b,diagramAction_linearField F hf hF a ha]
  rfl

/-- Nontrivial diagram action gives the literal graph/field factor order. -/
theorem graph_form_of_not_linearField {F : Type*} [Field F] [Finite F] [CharP F 2]
    {f : ℕ} (hf : 0<f) (hF : Nat.card F = 2^f) (a : MulAut PSL(3,F))
    (ha : a ∉ linearField F) :
    ∃ (g : GL (Fin 3) F) (σ : F ≃+* F),
      a = linearConj F g * graph F * fieldAction F σ := by
  have hstd : a ∈ standard F := by
    rw [standard_eq_top_of_two_power_card F hf hF]
    trivial
  obtain ⟨g,σ,h | h⟩ := Matrix.PSL3.CartanActions.NormalizerForm.standard_factorization
    F field_linearConj graph_linearConj_exists field_commute_graph a hstd
  · exact (ha (h ▸ (linearField F).mul_mem
      (Subgroup.mem_sup_left ⟨g,rfl⟩) (Subgroup.mem_sup_right ⟨σ,rfl⟩))).elim
  · refine ⟨g,σ,h.trans ?_⟩
    rw [mul_assoc,(field_commute_graph σ).eq,←mul_assoc]

/-- The original crossing has graph/field form in the original full quotient
marking. Its square and field part remain unrestricted. -/
theorem source_crossing_graph_form (s : SecondaryActionData c 2)
    {d : MSData c 2} (m : RootCoordinates d)
    (D : Chapter12.Section02.ChosenModule T L V) (hg : ActionGeneration s)
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 4)
    (mark : (s.component ⧸ pCore 2 s.component) ≃* PSL(3,F)) :
    ∃ (g : GL (Fin 3) F) (σ : F ≃+* F),
      (MulAut.congr mark)
        (s.action ⟨c.t,root_normalized c D c.crossing_mem⟩) =
      linearConj F g * graph F * fieldAction F σ := by
  obtain ⟨e,he⟩ := exists_inner_marking s mark
  have hfour : Nat.card F = 2^2 := hF
  obtain ⟨a,b,hR,hS⟩ := root_sylow_frame s D hg (by decide : 1<2) hfour e
  let t : rootNormalizer c := ⟨c.t,root_normalized c D c.crossing_mem⟩
  let z := s.action t
  let z₀ := (MulAut.congr mark) z
  let z₁ := (MulAut.congr a) z₀
  have hRI := binary_linear_radical_le_inner_of_mark s hg (by decide : 2≤2) hfour e
  obtain ⟨_,_,hSc,hRc⟩ := crossing_image_geometry s m (by decide : 1<2) D
  let J := image s (S c) ⊓ componentImage s
  let R := radicalImage s
  let J₀ := (J.subgroupOf (componentImage s)).map e.toMonoidHom
  let R₀ := (R.subgroupOf (componentImage s)).map e.toMonoidHom
  have hJ₀ : J₀.map z₀.toMonoidHom = J₀ :=
    model_image_preserves s mark e he J inf_le_right z hSc
  have hR₀ : R₀.map z₀.toMonoidHom ≠ R₀ := by
    intro hr
    apply hRc
    apply Subgroup.map_injective
      (f := (MulAut.congr mark).toMonoidHom) (MulAut.congr mark).injective
    rw [map_actor_congr,congr_inner]
    rw [←model_image_inner s mark e he R hRI,←inner_map_actor,hr]
  have hea : (e.trans a).toMonoidHom = a.toMonoidHom.comp e.toMonoidHom := by
    ext x
    rfl
  have hJframe : J₀.map a.toMonoidHom = unipotent F := by
    rw [Subgroup.map_map,←hea]
    exact hS
  have hRframe : R₀.map a.toMonoidHom = rootPlane F b := by
    rw [Subgroup.map_map,←hea]
    exact hR
  have hU : (unipotent F).map z₁.toMonoidHom = unipotent F := by
    rw [←hJframe,←map_actor_congr,hJ₀]
  have hr : (rootPlane F b).map z₁.toMonoidHom ≠ rootPlane F b := by
    intro hh
    apply hR₀
    apply Subgroup.map_injective (f := a.toMonoidHom) a.injective
    rw [map_actor_congr,hRframe]
    exact hh
  have hout := not_linearField_of_root_plane_moved (by decide : 0<2) hfour z₁ hU b hr
  apply graph_form_of_not_linearField (by decide : 0<2) hfour z₀
  intro hz₀
  apply hout
  have hk : z₀ ∈ (diagramAction F (by decide : 0<2) hfour).ker := by
    rwa [diagramAction_ker_eq_linearField]
  have hh := (inferInstance : (diagramAction F (by decide : 0<2) hfour).ker.Normal).conj_mem
    z₀ hk a
  rw [diagramAction_ker_eq_linearField] at hh
  have heq : a * z₀ * a⁻¹ = z₁ := by
    ext x
    rfl
  exact heq ▸ hh

end SecondaryActionData
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
