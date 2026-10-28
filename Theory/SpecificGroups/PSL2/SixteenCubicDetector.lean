module
public import Theory.SpecificGroups.PSL2.SixteenCubicBorel
public import Theory.GroupTheory.AutomorphismSquareWreath

/-!
# The kernel of the cubic detector on a PSL₂(16) Borel square

An automorphism preserving a binary PSL₂ Sylow acts on its Borel torus
by its field coefficient. If its restriction to the cubic roots is trivial,
it fixes the cubic residual modulo that Sylow. Inner conjugacy transports
this calculation to any specified Sylow. For a square, the detector also
records interchange, so a kernel element preserves each factor and the
single-factor calculation applies to both coordinates.

The Chapter14 consumer uses this displacement criterion through the literal
Mc/O₂(Mc) quotient, to force detector image order eight from earlier 14.6.12.
Source: Aschbacher--Smith 14.6.14, final paragraph, printed p.1033.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual
open Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.Semilinear
open Matrix.ProjectiveSpecialLinearGroup.OddBorel
namespace Theory.PSL2.SixteenCubicWreath
variable (F : Type*) [Field F] [Finite F] [CharP F 2]

omit [CharP F 2] in
private theorem units_cubic_residual (hF : Nat.card F = 16) :
    primeToResidual 3 Fˣ = rootsOfUnity 3 F := by
  have hc := FiniteField.CubicSixteen.roots_card F hF
  have hi : (rootsOfUnity 3 F).index = 5 := by
    have hh := (rootsOfUnity 3 F).card_mul_index
    rw [hc,Nat.card_units,hF] at hh
    omega
  exact le_antisymm (primeToResidual_le _ (by rw [hi]; decide))
    (le_primeToResidual_of_isPGroup (IsPGroup.of_card (n := 1) hc))

theorem cubicAction_inner (g : Theory.PSL2.Group F) :
    cubicAction F (MulAut.conj g) = 1 := by
  have h : fieldProjection F (MulAut.conj g) = 1 := by
    change MulAut.conj g ∈ (fieldProjection F).ker
    rw [fieldProjection_ker]
    exact ⟨g,rfl⟩
  change FiniteField.CubicSixteen.action F (fieldProjection F (MulAut.conj g)) = 1
  rw [h,map_one]

theorem cubic_kernel_displacement_standard
    (hF : Nat.card F = 16) (α : MulAut (Theory.PSL2.Group F))
    (hU : (kernel F).map α.toMonoidHom = kernel F)
    (hα : cubicAction F α = 1) (x : borel F)
    (hx : x ∈ primeToResidual 3 (borel F)) :
    (x : Theory.PSL2.Group F)⁻¹ * α x ∈ kernel F := by
  have hr : torusProjection F x ∈ rootsOfUnity 3 F := by
    rw [←units_cubic_residual F hF]
    exact map_primeToResidual_le (torusProjection F) (torusProjection_surjective F) (mem_map_of_mem _ hx)
  obtain ⟨y,hy,ht⟩ := cubicAction_borel_quotient F α hU x hr
  have ht' : torusProjection F y = torusProjection F x := by
    simpa only [hα,MulAut.one_apply] using ht
  have hh := (torusProjection_eq_one_iff F (x⁻¹*y)).mp (by
    rw [map_mul,map_inv,ht',inv_mul_cancel])
  simpa only [coe_mul,coe_inv,hy] using hh

theorem cubic_kernel_displacement
    (hF : Nat.card F = 16) (S : Sylow 2 (Theory.PSL2.Group F))
    (α : MulAut (Theory.PSL2.Group F))
    (hS : (S : Subgroup (Theory.PSL2.Group F)).map α.toMonoidHom = S)
    (hα : cubicAction F α = 1) (x : normalizer (S : Set (Theory.PSL2.Group F)))
    (hx : x ∈ primeToResidual 3 (normalizer (S : Set (Theory.PSL2.Group F)))) :
    (x : Theory.PSL2.Group F)⁻¹ * α x ∈ (S : Subgroup (Theory.PSL2.Group F)) := by
  obtain ⟨c,hcU,hcB⟩ := sylow_normalizer_conjugate F S
  let e := MulAut.conj c
  let β := MulAut.congr e.symm α
  have hb : (kernel F).map β.toMonoidHom = kernel F := by
    calc
      _ = (((kernel F).map e.toMonoidHom).map α.toMonoidHom).map e.symm.toMonoidHom := by
        rw [map_map,map_map]
        rfl
      _ = (S : Subgroup (Theory.PSL2.Group F)).map e.symm.toMonoidHom := by rw [hcU,hS]
      _ = kernel F := (map_symm_eq_iff_map_eq (kernel F) (e := e)).mpr hcU
  have hβ : cubicAction F β = 1 := by
    have he : β = e⁻¹ * α * e := rfl
    rw [he,map_mul,map_mul,map_inv,cubicAction_inner,hα]
    simp
  let b : borel F ≃* normalizer (S : Set (Theory.PSL2.Group F)) :=
    (e.subgroupMap (borel F)).trans (MulEquiv.subgroupCongr hcB)
  have hy : b.symm x ∈ primeToResidual 3 (borel F) := by
    rw [←map_primeToResidual b.symm]
    exact mem_map_of_mem _ hx
  have hh := cubic_kernel_displacement_standard F hF β hb hβ (b.symm x) hy
  have hh' := mem_map_of_mem e.toMonoidHom hh
  rw [hcU] at hh'
  have hval : e (b.symm x : Theory.PSL2.Group F) = x :=
    congrArg Subtype.val (b.apply_symm_apply x)
  simp only [map_mul,map_inv] at hh'
  change (e (b.symm x : Theory.PSL2.Group F))⁻¹ *
    e (e.symm (α (e (b.symm x : Theory.PSL2.Group F)))) ∈ (S : Subgroup (Theory.PSL2.Group F)) at hh'
  simpa only [e.apply_symm_apply,hval] using hh'
open WreathTwoElementaryRank AutomorphismSquare

theorem cubic_kernel_displacement_pair
    (hF : Nat.card F = 16) (S1 S2 : Sylow 2 (Theory.PSL2.Group F))
    (w : W (MulAut (Theory.PSL2.Group F)))
    (hS : ((S1 : Subgroup (Theory.PSL2.Group F)).prod (S2 : Subgroup (Theory.PSL2.Group F))).map
      (wreathHom w).toMonoidHom = (S1 : Subgroup (Theory.PSL2.Group F)).prod (S2 : Subgroup (Theory.PSL2.Group F)))
    (hw : cubicWreathAction F w = 1)
    (x : normalizer (((S1 : Subgroup (Theory.PSL2.Group F)).prod (S2 : Subgroup (Theory.PSL2.Group F))) : Set (Theory.PSL2.Group F × Theory.PSL2.Group F)))
    (hx : x ∈ primeToResidual 3 (normalizer
      (((S1 : Subgroup (Theory.PSL2.Group F)).prod (S2 : Subgroup (Theory.PSL2.Group F))) : Set (Theory.PSL2.Group F × Theory.PSL2.Group F)))) :
    (x : Theory.PSL2.Group F × Theory.PSL2.Group F)⁻¹ * wreathHom w x ∈
      (S1 : Subgroup (Theory.PSL2.Group F)).prod (S2 : Subgroup (Theory.PSL2.Group F)) := by
  have hr : w.right = 1 := congrArg RegularWreathProduct.right hw
  have ha (i : C2) : cubicAction F (w.left i) = 1 :=
    congrArg (fun z => z.left i) hw
  let U := (S1 : Subgroup (Theory.PSL2.Group F)).prod (S2 : Subgroup (Theory.PSL2.Group F))
  have h1 : (S1 : Subgroup (Theory.PSL2.Group F)).map (w.left 1).toMonoidHom = S1 := by
    apply eq_of_le_of_card_ge
    · rintro _ ⟨y,hy,rfl⟩
      have hh := hS ▸ mem_map_of_mem (wreathHom w).toMonoidHom
        (show (y,1) ∈ U from ⟨hy,one_mem _⟩)
      have hh' : (wreathMap w (y,1)).1 ∈ (S1 : Subgroup (Theory.PSL2.Group F)) := hh.1
      rw [wreathMap_apply,if_pos hr] at hh'
      exact hh'
    · rw [card_map_of_injective (w.left 1).injective]
  have h2 : (S2 : Subgroup (Theory.PSL2.Group F)).map (w.left turn).toMonoidHom = S2 := by
    apply eq_of_le_of_card_ge
    · rintro _ ⟨y,hy,rfl⟩
      have hh := hS ▸ mem_map_of_mem (wreathHom w).toMonoidHom
        (show (1,y) ∈ U from ⟨one_mem _,hy⟩)
      have hh' : (wreathMap w (1,y)).2 ∈ (S2 : Subgroup (Theory.PSL2.Group F)) := hh.2
      rw [wreathMap_apply,if_pos hr] at hh'
      exact hh'
    · rw [card_map_of_injective (w.left turn).injective]
  let f := MonoidHom.fst (Theory.PSL2.Group F) (Theory.PSL2.Group F)
  let g := MonoidHom.snd (Theory.PSL2.Group F) (Theory.PSL2.Group F)
  have hf : U.map f = S1 := by
    apply le_antisymm
    · rintro _ ⟨y,hy,rfl⟩; exact hy.1
    · intro y hy; exact ⟨(y,1),⟨hy,one_mem _⟩,rfl⟩
  have hg : U.map g = S2 := by
    apply le_antisymm
    · rintro _ ⟨y,hy,rfl⟩; exact hy.2
    · intro y hy; exact ⟨(1,y),⟨one_mem _,hy⟩,rfl⟩
  let f' : normalizer (U : Set (Theory.PSL2.Group F × Theory.PSL2.Group F)) →* normalizer (S1 : Set _) :=
    (f.comp (normalizer (U : Set (Theory.PSL2.Group F × Theory.PSL2.Group F))).subtype).codRestrict _ (fun y => by
      have hh := le_normalizer_map f (mem_map_of_mem f y.property)
      change f y ∈ normalizer (S1 : Set (Theory.PSL2.Group F))
      simpa only [hf,Sylow.coe_coe] using hh)
  let g' : normalizer (U : Set (Theory.PSL2.Group F × Theory.PSL2.Group F)) →* normalizer (S2 : Set _) :=
    (g.comp (normalizer (U : Set (Theory.PSL2.Group F × Theory.PSL2.Group F))).subtype).codRestrict _ (fun y => by
      have hh := le_normalizer_map g (mem_map_of_mem g y.property)
      change g y ∈ normalizer (S2 : Set (Theory.PSL2.Group F))
      simpa only [hg,Sylow.coe_coe] using hh)
  have hx1 := map_primeToResidual_le_of_hom 3 f' (mem_map_of_mem f' hx)
  have hx2 := map_primeToResidual_le_of_hom 3 g' (mem_map_of_mem g' hx)
  have hh1 := cubic_kernel_displacement F hF S1 (w.left 1) h1 (ha 1) (f' x) hx1
  have hh2 := cubic_kernel_displacement F hF S2 (w.left turn) h2 (ha turn) (g' x) hx2
  change ((x.val).1⁻¹ * (wreathMap w x.val).1 ∈ S1) ∧
    ((x.val).2⁻¹ * (wreathMap w x.val).2 ∈ S2)
  rw [wreathMap_apply,if_pos hr]
  exact ⟨hh1,hh2⟩

/-- The same kernel calculation for any specified Sylow of the square. -/
theorem cubic_kernel_displacement_square
    (hF : Nat.card F = 16) (S : Sylow 2 (Theory.PSL2.Group F × Theory.PSL2.Group F))
    (w : W (MulAut (Theory.PSL2.Group F)))
    (hS : (S : Subgroup (Theory.PSL2.Group F × Theory.PSL2.Group F)).map
      (wreathHom w).toMonoidHom = S)
    (hw : cubicWreathAction F w = 1)
    (x : normalizer (S : Set (Theory.PSL2.Group F × Theory.PSL2.Group F)))
    (hx : x ∈ primeToResidual 3 (normalizer (S : Set (Theory.PSL2.Group F × Theory.PSL2.Group F)))) :
    (x : Theory.PSL2.Group F × Theory.PSL2.Group F)⁻¹ * wreathHom w x ∈
      (S : Subgroup (Theory.PSL2.Group F × Theory.PSL2.Group F)) := by
  let f := MonoidHom.fst (Theory.PSL2.Group F) (Theory.PSL2.Group F)
  let g := MonoidHom.snd (Theory.PSL2.Group F) (Theory.PSL2.Group F)
  let S1 := S.mapSurjective (f := f) (fun x => ⟨(x,1),rfl⟩)
  let S2 := S.mapSurjective (f := g) (fun x => ⟨(1,x),rfl⟩)
  have hp : IsPGroup 2 ((S1 : Subgroup (Theory.PSL2.Group F)).prod (S2 : Subgroup (Theory.PSL2.Group F))) := by
    obtain ⟨m,hm⟩ := S1.isPGroup'.exists_card_eq
    obtain ⟨n,hn⟩ := S2.isPGroup'.exists_card_eq
    exact IsPGroup.of_card (n := m+n) (by
      rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv,Nat.card_prod,hm,hn,pow_add])
  have he : (S1 : Subgroup (Theory.PSL2.Group F)).prod (S2 : Subgroup (Theory.PSL2.Group F)) = (S : Subgroup _) :=
    S.is_maximal' hp (fun y hy => ⟨mem_map_of_mem f hy,mem_map_of_mem g hy⟩)
  let e := MulEquiv.subgroupCongr (congrArg (fun U : Subgroup (Theory.PSL2.Group F × Theory.PSL2.Group F) =>
    normalizer (U : Set (Theory.PSL2.Group F × Theory.PSL2.Group F))) he.symm)
  have hx' : e x ∈ primeToResidual 3 (normalizer
      (((S1 : Subgroup (Theory.PSL2.Group F)).prod (S2 : Subgroup (Theory.PSL2.Group F))) : Set (Theory.PSL2.Group F × Theory.PSL2.Group F))) := by
    rw [←map_primeToResidual e]
    exact mem_map_of_mem _ hx
  have hh := cubic_kernel_displacement_pair F hF S1 S2 w (by simpa only [he] using hS) hw (e x) hx'
  have hh' : x.val⁻¹ * wreathHom w x.val ∈ (S1 : Subgroup (Theory.PSL2.Group F)).prod (S2 : Subgroup (Theory.PSL2.Group F)) := hh
  simpa only [he] using hh'

end Theory.PSL2.SixteenCubicWreath
