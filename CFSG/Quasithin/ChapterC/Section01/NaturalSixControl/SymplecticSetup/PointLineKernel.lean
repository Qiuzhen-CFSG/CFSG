module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.NoncentralSeedChoice
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointCoreFixedLine
public import Theory.GroupTheory.InvolutionCentralizerControl
/-!
# A moving line determines the native edge kernel

The moving layer meets every adjacent edge layer in a subgroup of order two.
A nonzero subgroup of that intersection is therefore the whole fixed line.
In the original source coordinates, the full point-core image is the two-core
of the marked vector stabilizer, so the line centralizer normalizes the edge
radical. The literal source embedding transports this to every edge.

Neighbor transitivity conjugates one adjacent edge kernel to another. If the
same moving line lies in both edge layers, the conjugator normalizes that
order-two line and hence fixes it pointwise; the first result makes the two
kernels equal. The SourceData application retains the actual reduction.

Source: MS93 (5.9), printed pp.920--921; the natural point-stabilizer geometry
is Aschbacher--Smith B.3.4 and Notation 13.2.1.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BinaryPermutation
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M} [L.Normal] [W.Normal]
  (s : Source L R W)

/-- The fixed moving line in the original finite source controls its radical. -/
theorem module_seed_centralizer_normalizes_radical (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom) :
    centralizer (W⊓omegaCenter R:Set M)≤normalizer (R:Set M) := by
  have hp : R.map s.projection=pointCore.map (MulAut.conj u).toMonoidHom := by
    simpa only [Model.pointCore_eq_exceptional] using hfull
  have hpre : (pointCore.map (MulAut.conj u).toMonoidHom).comap s.projection=R := by
    rw [←hp,comap_map_eq,s.projection_kernel,sup_eq_left.mpr s.core_le]
  let w : W := s.coordinates.symm (Multiplicative.ofAdd
    (Model.rho u (NaturalGeometry.pairVector 4 5)))
  have hw : (s.coordinates w).toAdd=Model.rho u (NaturalGeometry.pairVector 4 5) := by
    exact congrArg Multiplicative.toAdd (s.coordinates.apply_symm_apply _)
  have hwfix (r:M) (hr:r∈R) : MulAut.conjNormal r w=w := by
    apply s.coordinates.injective
    apply Multiplicative.toAdd.injective
    rw [s.action,hw]
    exact PointCoreFixedLine.conjugate_core_fixes u (s.projection r)
      (hp ▸ mem_map_of_mem s.projection hr)
  have hwseed : (w:M)∈W⊓omegaCenter R := by
    rw [s.module_inf_seed_eq_fixed]
    refine ⟨w.property,?_⟩
    intro r hr
    exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val (hwfix r hr))
  intro m hm
  have hmfix : MulAut.conjNormal m w=w := by
    apply Subtype.ext
    change m*(w:M)*m⁻¹=(w:M)
    rw [←hm (w:M) hwseed,mul_inv_cancel_right]
  have hh := s.action m w
  rw [hmfix,hw] at hh
  have hmN := PointCoreFixedLine.normalizes_core_of_fixes u (s.projection m) hh.symm
  have hn := (pointCore.map (MulAut.conj u).toMonoidHom).le_normalizer_comap s.projection hmN
  rwa [hpre] at hn

private theorem pointLine_coordinates (h : NativeCentralLayer s) {a t : Vertex R}
    (ha : color R a=false) (hat : Adjacent R a t) :
    ∃ i : M→*FreeAmalgam R, Function.Injective i ∧ i.range=stabilizer R a ∧
      R.map i=Q R t ∧ W.map i=U R a ∧ (omegaCenter R).map i=Z R t := by
  obtain ⟨g,hg|hg⟩ := (adjacent_iff_exists_common R a t).mp hat
  · rcases hg with ⟨rfl,rfl⟩
    let i := (MulAut.conj g⁻¹).toMonoidHom.comp (embedM R)
    refine ⟨i,(MulAut.conj g⁻¹).injective.comp (embedM_injective R),?_,?_,?_,?_⟩
    · rw [MonoidHom.range_comp]
      change (Mbar R).map (MulAut.conj g⁻¹).toMonoidHom=stabilizer R (mVertex R g)
      exact (stabilizer_mVertex R g).symm
    · have he := Q_act R g (beta R)
      rw [Q_beta] at he
      simpa only [beta,act_hVertex,one_mul,map_map] using he.symm
    · have he := U_act R g (alpha R)
      rw [h.U_eq_module] at he
      simpa only [alpha,act_mVertex,one_mul,map_map] using he.symm
    · have hseed : Z R (beta R)=(omegaCenter R).map (embedM R) := by
        rw [Z,if_neg (by exact Bool.noConfusion : color R (beta R)≠false),edgeOmega,Q_beta,
          omegaCenter_map _ _ (embedM_injective R)]
      have he := Z_act R g (beta R)
      rw [hseed] at he
      simpa only [beta,act_hVertex,one_mul,map_map] using he.symm
  · rw [hg.1] at ha
    cases ha

/-- The vertex centralizer of a nonzero moving edge line normalizes its kernel. -/
theorem edge_line_centralizer_normalizes_kernel (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    {a t : Vertex R} (ha : color R a=false) (hat : Adjacent R a t)
    (H : Subgroup (FreeAmalgam R)) (hH : H≤U R a⊓Z R t) (hne : H≠⊥) :
    stabilizer R a⊓centralizer (H:Set (FreeAmalgam R))≤normalizer (Q R t:Set (FreeAmalgam R)) := by
  have he : H=U R a⊓Z R t := by
    let := finite_Z R t
    let : Finite (U R a⊓Z R t:Subgroup (FreeAmalgam R)) :=
      Finite.of_injective (inclusion inf_le_right) (inclusion_injective _)
    let : Finite H := Finite.of_injective (inclusion hH) (inclusion_injective _)
    apply eq_of_le_of_card_ge hH
    rw [s.moving_inf_edge_card h u hfull ha hat]
    exact (one_lt_card_iff_ne_bot H).mpr hne
  obtain ⟨i,hi,hiG,hiR,hiW,hiZ⟩ := s.pointLine_coordinates h ha hat
  rw [←hiR]
  intro m hm
  obtain ⟨x,rfl⟩ := hiG ▸ hm.1
  apply (R.le_normalizer_map i)
  apply mem_map_of_mem
  apply s.module_seed_centralizer_normalizes_radical u hfull
  intro w hw
  apply hi
  have hmC := hm.2 (i w)
  rw [he,←hiW,←hiZ,←Subgroup.map_inf _ _ i hi] at hmC
  simpa only [map_mul] using hmC (mem_map_of_mem i hw)
/-- Adjacent edge layers containing the same nonzero moving line have equal kernels. -/
theorem edge_kernel_eq_of_common_moving_line (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    {a t t' : Vertex R} (ha : color R a=false)
    (hat : Adjacent R a t) (hat' : Adjacent R a t')
    (H : Subgroup (FreeAmalgam R)) (hH : H≤U R a⊓Z R t) (hne : H≠⊥)
    (hHt' : H≤Z R t') : Q R t'=Q R t := by
  have he (b : Vertex R) (hab : Adjacent R a b) (hHb : H≤U R a⊓Z R b) :
      H=U R a⊓Z R b := by
    let := finite_Z R b
    let : Finite (U R a⊓Z R b:Subgroup (FreeAmalgam R)) :=
      Finite.of_injective (inclusion inf_le_right) (inclusion_injective _)
    let : Finite H := Finite.of_injective (inclusion hHb) (inclusion_injective _)
    apply eq_of_le_of_card_ge hHb
    rw [s.moving_inf_edge_card h u hfull ha hab]
    exact (one_lt_card_iff_ne_bot H).mpr hne
  have hHa := he t hat hH
  have hHb := he t' hat' (le_inf (hH.trans inf_le_left) hHt')
  have hcard : Nat.card H=2 := hHa ▸ s.moving_inf_edge_card h u hfull ha hat
  obtain ⟨g,hg,hgt⟩ := stabilizer_transitive_neighbors R a hat hat'
  have hga : act R g a=a := hg
  have hmap : H.map (MulAut.conj g⁻¹).toMonoidHom=H := by
    calc
      H.map (MulAut.conj g⁻¹).toMonoidHom =
          (U R a⊓Z R t).map (MulAut.conj g⁻¹).toMonoidHom := congrArg (map _) hHa
      _ = U R a⊓Z R t' := by
        rw [Subgroup.map_inf _ _ _ (MulAut.conj g⁻¹).injective,←U_act,←Z_act,hga,hgt]
      _ = H := hHb.symm
  have hgC := normalizer_le_centralizer_of_card_two H hcard
    (mem_normalizer_iff_map_conj_eq.mpr hmap)
  have hgQ := s.edge_line_centralizer_normalizes_kernel h u hfull ha hat H hH hne
    ⟨(stabilizer R a).inv_mem hg,hgC⟩
  rw [←hgt,Q_act]
  exact mem_normalizer_iff_map_conj_eq.mp hgQ

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
variable {K : Type*} [Group K] [Finite K] {L W : Subgroup K} [L.Normal] [W.Normal]
  {T : Sylow 2 K} (d : NaturalSixControl.SourceData L W T)

/-- In the actual characteristic replacement, the fixed moving line controls
its edge kernel, or the alternating-block alternative holds. -/
theorem reducedSource_block_or_point_line_kernel (hm : IntrinsicMSPair d)
    (r : CharacteristicReduction (L.subgroupOf (L⊔d.B)) (d.B.subgroupOf (L⊔d.B))) :
    IsAlternatingBlock L 6 ∨
      ∀ (a t : Vertex r.radical), color r.radical a=false → Adjacent r.radical a t →
      ∀ H : Subgroup (FreeAmalgam r.radical), H≤U r.radical a⊓Z r.radical t → H≠⊥ →
        (stabilizer r.radical a⊓centralizer (H:Set (FreeAmalgam r.radical))≤
          normalizer (Q r.radical t:Set (FreeAmalgam r.radical))) ∧
        ∀ t' : Vertex r.radical, Adjacent r.radical a t' → H≤Z r.radical t' →
          Q r.radical t'=Q r.radical t := by
  rcases reducedSource_block_or_full_point_image d hm r with hb|hf
  · exact Or.inl hb
  · let s := (originalSource d hm).reduce r
    have hn := reduced_nativeCentralLayer d hm r
    have he : r.radical.map s.projection=Model.E.map
        (MulAut.conj d.relabeler.val⁻¹).toMonoidHom := by
      simpa only [Model.pointCore_eq_exceptional] using hf
    refine Or.inr (fun a t ha hat H hH hne => ⟨?_,?_⟩)
    · exact s.edge_line_centralizer_normalizes_kernel hn _ he ha hat H hH hne
    · intro t' hat' hHt'
      exact s.edge_kernel_eq_of_common_moving_line hn _ he ha hat hat' H hH hne hHt'
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
