module

public import Theory.Representation.BinaryNaturalDual.FiveActors.Basic
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.RadicalOrientation.Duality

/-!
# Actual radical conjugators in degree five

Linear equivalences extend isomorphisms between subspaces of equal
dimension. Inverse transpose carries a radical into the radical at its
dot-product annihilator. Thus a radical at either a two-space or a
three-space can be carried into the radical at any prescribed three-space.
Naturality of the inner embedding transports these actual automorphisms
to conjugation in `Aut(GL₅(2))`.

Source application: Aschbacher–Smith, combined manuscript (1 March 2004),
H.9.2(3), printed pp.390–391. No classification of elementary subgroups is
assumed or asserted by these transport results.
-/

@[expose] public section

open BinaryLinear BinaryLinear.OuterCyclic Matrix
namespace BinaryNaturalDual.FiveActors.Classification

noncomputable def perp (W : Submodule (ZMod 2) X) : Submodule (ZMod 2) X :=
  W.dualAnnihilator.comap (dotProductEquiv (ZMod 2) (Fin 5)).toLinearMap

theorem mem_perp (W : Submodule (ZMod 2) X) (x : X) :
    x ∈ perp W ↔ ∀ y ∈ W, dotProduct x y = 0 := by
  exact Submodule.mem_dualAnnihilator _

private noncomputable def perpEquiv (W : Submodule (ZMod 2) X) :
    perp W ≃ₗ[ZMod 2] W.dualAnnihilator where
  toFun x := ⟨dotProductEquiv (ZMod 2) (Fin 5) x.val, x.property⟩
  invFun f := ⟨(dotProductEquiv (ZMod 2) (Fin 5)).symm f.val,
    by change dotProductEquiv (ZMod 2) (Fin 5) _ ∈ W.dualAnnihilator; simp only [LinearEquiv.apply_symm_apply]; exact f.property⟩
  left_inv x := by apply Subtype.ext; simp
  right_inv f := by apply Subtype.ext; simp
  map_add' x y := by apply Subtype.ext; exact map_add _ _ _
  map_smul' a x := by apply Subtype.ext; exact map_smul _ _ _

theorem finrank_perp (W : Submodule (ZMod 2) X) :
    Module.finrank (ZMod 2) (perp W) = 5 - Module.finrank (ZMod 2) W := by
  have h := Subspace.finrank_add_finrank_dualAnnihilator_eq W
  have he := (perpEquiv W).finrank_eq
  have hx : Module.finrank (ZMod 2) X = 5 := by simp [X]
  omega

private theorem graph_pair_inv (g : G) (x y : X) :
    dotProduct (graphLinear 5 g x) y = dotProduct x (g⁻¹ y) := by
  simpa only [LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply] using
    graphLinear_dotProduct g x (g⁻¹ y)

theorem radical_graph_le (W : Submodule (ZMod 2) X) :
    (radical W).map (graphLinear 5).toMonoidHom ≤ radical (perp W) := by
  rintro _ ⟨g, hg, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom]
  have hgi := (radical W).inv_mem hg
  constructor
  · intro x hx
    have he (y : X) : dotProduct (graphLinear 5 g x) y = dotProduct x y := by
      rw [graph_pair_inv]
      have h := (mem_perp W x).mp hx (g⁻¹ y - y) (hgi.2 y)
      simpa only [dotProduct_sub, sub_eq_zero] using h
    funext i
    simpa only [dotProduct_single, mul_one] using he (Pi.single i 1)
  · intro x
    apply (mem_perp W _).mpr
    intro y hy
    rw [sub_dotProduct, graph_pair_inv, hgi.1 y hy, sub_self]

theorem exists_map_subspace_eq (W U : Submodule (ZMod 2) X)
    (h : Module.finrank (ZMod 2) W = Module.finrank (ZMod 2) U) :
    ∃ g : G, W.map g.toLinearMap = U := by
  let e := LinearEquiv.ofFinrankEq W U h
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq e
  refine ⟨g, ?_⟩
  ext x
  constructor
  · rintro ⟨w, hw, rfl⟩
    have he := hg ⟨w, hw⟩
    exact he ▸ (e ⟨w, hw⟩).property
  · intro hx
    refine ⟨(e.symm ⟨x, hx⟩).val, (e.symm ⟨x, hx⟩).property, ?_⟩
    change g (e.symm ⟨x, hx⟩).val = x
    rw [← hg]
    exact congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)

theorem inner_image_map_conj (E : Subgroup G) (a : M) :
    (E.map MulAut.conj).map (MulAut.conj a).toMonoidHom =
      (E.map a.toMonoidHom).map MulAut.conj := by
  simp only [Subgroup.map_map]
  congr 1
  ext g x
  simp [MulAut.conj_apply]

theorem radicalActor_map_conj (W : Submodule (ZMod 2) X) (g : G) :
    (radicalActor W).map (MulAut.conj (MulAut.conj g)).toMonoidHom =
      radicalActor (W.map g.toLinearMap) := by
  rw [radicalActor, inner_image_map_conj, radical_map_conj]
  rfl

theorem radicalActor_conjugate (W U : Submodule (ZMod 2) X)
    (h : Module.finrank (ZMod 2) W = Module.finrank (ZMod 2) U) :
    ∃ a : M, (radicalActor W).map (MulAut.conj a).toMonoidHom = radicalActor U := by
  obtain ⟨g, hg⟩ := exists_map_subspace_eq W U h
  exact ⟨MulAut.conj g, by rw [radicalActor_map_conj, hg]⟩

theorem exists_map_radical_le (W U : Submodule (ZMod 2) X)
    (hW : Module.finrank (ZMod 2) W = 2 ∨ Module.finrank (ZMod 2) W = 3)
    (hU : Module.finrank (ZMod 2) U = 3) :
    ∃ a : M, (radical W).map a.toMonoidHom ≤ radical U := by
  rcases hW with hW | hW
  · have hp : Module.finrank (ZMod 2) (perp W) = Module.finrank (ZMod 2) U := by
      rw [finrank_perp, hW, hU]
    obtain ⟨g, hg⟩ := exists_map_subspace_eq (perp W) U hp
    refine ⟨MulAut.conj g * graphLinear 5, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    change (MulAut.conj g) (graphLinear 5 x) ∈ radical U
    have hm : (MulAut.conj g) (graphLinear 5 x) ∈
        (radical (perp W)).map (MulAut.conj g).toMonoidHom :=
      ⟨graphLinear 5 x, radical_graph_le W ⟨x, hx, rfl⟩, rfl⟩
    rwa [radical_map_conj, hg] at hm
  · obtain ⟨g, hg⟩ := exists_map_subspace_eq W U (hW.trans hU.symm)
    exact ⟨MulAut.conj g, by rw [radical_map_conj, hg]⟩

end BinaryNaturalDual.FiveActors.Classification
