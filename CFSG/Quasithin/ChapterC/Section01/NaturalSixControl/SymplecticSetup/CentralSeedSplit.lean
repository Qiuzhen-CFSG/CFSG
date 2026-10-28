module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.PointFixed
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.EdgeLayer

/-!
# Splitting the actual symplectic seed layer

The point-core fixed-vector bound puts each edge seed element in the product
of the natural module and the component-fixed subgroup. These normal factors
are disjoint, so the edge kernel fixes each factor separately. The second
factor then centralizes both the component and the edge kernel, which generate
the vertex group. Taking the seed's normal closure splits the actual Z-layer
as its natural moving layer times its intersection with the vertex center.

The element-level conclusion preserves both factors and their literal graph
embedding. It supplies the noncentral seed choice in MS93 (5.9), printed
pp.920--922, using the native full point-core branch of (5.3).
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M]
variable {L R W : Subgroup M} [L.Normal] [W.Normal] (s : Source L R W)

theorem ambient_seed_le_module_sup_center (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection = Model.E.map (MulAut.conj u).toMonoidHom) :
    omegaCenter R ≤ W ⊔ center M := by
  let X := Source.ambientX (M:=M)
  let F := X ⊓ centralizer (L : Set M)
  let : X.Normal := s.ambientX_normal
  let : F.Normal := inferInstance
  have hdis : Disjoint W F := by
    apply disjoint_iff.mpr
    exact le_antisymm ((inf_le_inf_left W inf_le_right).trans_eq
      s.module_inf_component_centralizer_eq_bot) bot_le
  have hp : R.map s.projection =
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map (MulAut.conj u).toMonoidHom := by
    simpa only [Model.pointCore_eq_exceptional] using hfull
  intro z hz
  have hzX : z ∈ X := by
    apply (mem_map_iff_mem (embedM_injective R)).mp
    rw [←s.X_alpha_eq]
    apply s.Z_le_X
    rw [SymplecticSeed.Z_eq_seedHull]
    exact mem_map_of_mem _ (subset_normalClosure hz)
  have hzR : z ∈ centralizer (R:Set M) := (mem_omegaCenter_iff.mp hz).2.2
  have hzWF : z ∈ W ⊔ F := s.ambientX_fixed_point_le
    (s.projection_surjective_of_radical_image_le_conjugate u hfull.le) h u hp ⟨hzX,hzR⟩
  obtain ⟨w,hw,d,hd,hwd⟩ := mem_sup_of_normal_right.mp hzWF
  have hdR : d ∈ centralizer (R:Set M) := by
    intro r hr
    have hconj : r*z*r⁻¹=z := by rw [hzR r hr,mul_inv_cancel_right]
    have he : (r*w*r⁻¹)*(r*d*r⁻¹)=w*d := by
      calc
        (r*w*r⁻¹)*(r*d*r⁻¹) = r*(w*d)*r⁻¹ := by group
        _ = w*d := by rw [hwd,hconj]
    have he' : (⟨r*w*r⁻¹,(inferInstance : W.Normal).conj_mem w hw r⟩ : W) = ⟨w,hw⟩ ∧
        (⟨r*d*r⁻¹,(inferInstance : F.Normal).conj_mem d hd r⟩ : F) = ⟨d,hd⟩ :=
      Prod.mk.inj (mul_injective_of_disjoint hdis he)
    have hdconj : r*d*r⁻¹=d := congrArg Subtype.val he'.2
    exact mul_inv_eq_iff_eq_mul.mp hdconj
  have hdC : d ∈ center M := by
    apply mem_center_iff.mpr
    intro m
    obtain ⟨l,hl,r,hr,rfl⟩ := s.product m
    calc
      (l*r)*d = l*(r*d) := mul_assoc _ _ _
      _ = l*(d*r) := by rw [hdR r hr]
      _ = (d*l)*r := by rw [←mul_assoc,hd.2 l hl]
      _ = d*(l*r) := mul_assoc _ _ _
  rw [←hwd]
  exact mul_mem_sup hw hdC

theorem seedHull_eq_module_sup_center (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection = Model.E.map (MulAut.conj u).toMonoidHom) :
    normalClosure (omegaCenter R:Set M) = W ⊔
      (normalClosure (omegaCenter R:Set M) ⊓ center M) := by
  let H := normalClosure (omegaCenter R:Set M)
  have hWH : W ≤ H := by
    dsimp only [H]
    rw [s.seedHull_eq_module_sup_seed h]
    exact le_sup_left
  have hH : H ≤ W ⊔ center M := by
    apply normalClosure_le_normal
    exact s.ambient_seed_le_module_sup_center h u hfull
  apply le_antisymm
  · intro z hz
    obtain ⟨w,hw,d,hd,hwd⟩ := mem_sup_of_normal_right.mp (hH hz)
    rw [←hwd]
    apply mul_mem_sup hw
    refine ⟨?_,hd⟩
    have he : d=w⁻¹*z := by rw [←hwd]; group
    rw [he]
    exact H.mul_mem (H.inv_mem (hWH hw)) hz
  · exact sup_le hWH inf_le_left

omit [Finite M] [L.Normal] [W.Normal] in
private theorem center_map_le_vertex_center : (center M).map (embedM R) ≤
      (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype := by
    rintro _ ⟨z,hz,rfl⟩
    have hzG : embedM R z ∈ stabilizer R (alpha R) := by
      rw [show alpha R = mVertex R 1 from rfl,stabilizer_m_base]
      exact ⟨z,rfl⟩
    refine ⟨⟨embedM R z,hzG⟩,?_,rfl⟩
    apply mem_center_iff.mpr
    intro x
    apply Subtype.ext
    have hx : x.val ∈ (embedM R).range := by
      exact (show stabilizer R (alpha R) = (embedM R).range from stabilizer_m_base R) ▸ x.property
    obtain ⟨m,hm⟩ := hx
    change x.val * embedM R z = embedM R z * x.val
    rw [←hm,←map_mul,←map_mul,mem_center_iff.mp hz m]

/-- The original Z-layer splits over the center of its vertex group. -/
theorem Z_eq_moving_sup_central (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection = Model.E.map (MulAut.conj u).toMonoidHom) :
    Z R (alpha R) = U R (alpha R) ⊔
      (Z R (alpha R) ⊓ (center (stabilizer R (alpha R))).map
        (stabilizer R (alpha R)).subtype) := by
  have hUZ : U R (alpha R) ≤ Z R (alpha R) := by
    rw [h.U_eq_module]; exact s.module_le_Z
  apply le_antisymm
  · conv_lhs => rw [SymplecticSeed.Z_eq_seedHull,s.seedHull_eq_module_sup_center h u hfull,
      Subgroup.map_sup,←h.U_eq_module]
    apply sup_le le_sup_left
    apply le_trans _ le_sup_right
    apply le_inf
    · exact map_mono inf_le_left |>.trans_eq (SymplecticSeed.Z_eq_seedHull R).symm
    · exact (map_mono inf_le_right).trans center_map_le_vertex_center
  · exact sup_le hUZ inf_le_left

/-- The splitting retains the actual moving and central factors of an element. -/
theorem exists_moving_central_factors (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection = Model.E.map (MulAut.conj u).toMonoidHom)
    {z : FreeAmalgam R} (hz : z ∈ Z R (alpha R)) :
    ∃ w ∈ U R (alpha R), ∃ d ∈ Z R (alpha R) ⊓
      (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype,
      w*d=z := by
  rw [SymplecticSeed.Z_eq_seedHull] at hz
  obtain ⟨z,hz,rfl⟩ := hz
  rw [s.seedHull_eq_module_sup_center h u hfull] at hz
  obtain ⟨w,hw,d,hd,hwd⟩ := mem_sup_of_normal_left.mp hz
  refine ⟨embedM R w,?_,embedM R d,⟨?_,?_⟩,?_⟩
  · rw [h.U_eq_module]
    exact mem_map_of_mem _ hw
  · rw [SymplecticSeed.Z_eq_seedHull]
    exact mem_map_of_mem _ hd.1
  · exact center_map_le_vertex_center (mem_map_of_mem _ hd.2)
  · rw [←map_mul,hwd]

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
