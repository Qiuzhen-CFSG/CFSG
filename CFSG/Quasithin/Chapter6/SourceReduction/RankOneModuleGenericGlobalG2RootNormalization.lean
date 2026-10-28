module
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.InnerFieldCoverage.FrameAlignment
import all Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.InnerFieldCoverage.FrameAlignment.WeylCorrection
import all Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.InnerFieldCoverage.FrameAlignment.RootRecovery

/-!
# The six roots under compatible torus-preserving parabolic actions

The center of the positive unipotent group identifies its highest A root.
In the short parabolic, a torus-preserving automorphism takes its Weyl
involution to the same torus coset. It consequently preserves the scalar
torus, whose centralizer in the unipotent group is exactly the F root.
The two Weyl actions then recover B, E, D and C. This argument includes
field order four and never extends a local action to the full G₂ model.

Finite injectivity upgrades the six root actions to additive equivalences.
Their product is the literal coordinate action consumed by the q³ fixed-point
bound. The companion G2OuterRootAction constructs these local actions from
the original Sylow actor and the same compatible parabolic comparison.

Source: Aschbacher–Smith F.4.29(2), F.4.37–38, printed pp.289,293–294
(`refs/quasithin.pdf`). The imported octonion formulas retain the ATLAS
attribution in LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
The internal imports reuse Weyl identities without widening their public APIs.
-/

public noncomputable section
open Subgroup Atlas.G2 Atlas.G2.LieParabolicSetup
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.G2OuterRootNormalization
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem scalar_torus_centralizer (hq : 2 < Nat.card F)
    (x : Model F) (hx : x ∈ unipotent)
    (hc : ∀ l : Fˣ, Commute (torus l l) x) : ∃ a : F, x=rootF a := by
  rw [unipotent_eq_range] at hx
  obtain ⟨v,rfl⟩ := hx
  have hu : 1 < Nat.card Fˣ := by rw [Nat.card_units]; omega
  let : Nontrivial Fˣ := Finite.one_lt_card_iff_nontrivial.mp hu
  obtain ⟨l,hl⟩ := exists_ne (1:Fˣ)
  have hl1 : (l:F)≠1 := fun hh => hl (Units.ext hh)
  have hl2 : (l:F)^2≠1 := by
    intro he
    apply hl1
    apply frobenius_inj F 2
    change (l:F)^2=1^2
    simpa only [one_pow] using he
  have he : torusUnipotentParameters l l v=v := by
    apply unipotentProduct_injective
    rw [←torus_unipotentProduct,(hc l).eq,mul_inv_cancel_right]
  have h0 := congrFun he 0
  have h1 := congrFun he 1
  have h2 := congrFun he 2
  have h3 := congrFun he 3
  have h4 := congrFun he 4
  simp [torusUnipotentParameters,pow_two] at h0 h1 h2 h3 h4
  have hv0 : v 0=0 := eq_zero_of_mul_eq_self_left hl2 (by simpa only [pow_two,mul_assoc] using h0)
  have hv1 : v 1=0 := eq_zero_of_mul_eq_self_left hl1 h1
  have hv2 : v 2=0 := eq_zero_of_mul_eq_self_left hl1 h2
  have hv3 : v 3=0 := eq_zero_of_mul_eq_self_left hl1 h3
  have hv4 : v 4=0 := eq_zero_of_mul_eq_self_left hl1 h4
  exact ⟨v 5,by simp [unipotentProduct,hv0,hv1,hv2,hv3,hv4]⟩



open Atlas.G2.LieAutomorphismExtensions.InnerFieldCoverage

omit [Finite F] [CharP F 2] in
private theorem weyl_image (P : Subgroup (Model F))
    (hDP : splitTorus ≤ P) (b : MulAut P)
    (hD : (splitTorus.subgroupOf P).map b.toMonoidHom = splitTorus.subgroupOf P)
    (w : Model F) (hw : w ∈ P) (hwN : w ∈ normalizer (splitTorus (K := F) : Set (Model F)))
    (hwD : w ∉ splitTorus) (hcover : RankOneTorusNormalizerCover P w) :
    ∃ l m : Fˣ, (b ⟨w,hw⟩).val = torus l m * w := by
  have hn : (⟨w,hw⟩ : P) ∈ normalizer (splitTorus.subgroupOf P : Set P) :=
    mem_normalizer_iff.mpr (fun x => mem_normalizer_iff.mp hwN x.val)
  have hh := (splitTorus.subgroupOf P).le_normalizer_map b.toMonoidHom
    (mem_map_of_mem _ hn)
  rw [hD] at hh
  have hN := (splitTorus.subgroupOf P).le_normalizer_map P.subtype (mem_map_of_mem _ hh)
  rw [map_subgroupOf_eq_of_le hDP] at hN
  rcases hcover _ (b ⟨w,hw⟩).property hN with he | he
  · have hmem : b ⟨w,hw⟩ ∈ (splitTorus.subgroupOf P).map b.toMonoidHom := by rw [hD]; exact he
    have hh : (⟨w,hw⟩ : P) ∈ splitTorus.subgroupOf P := (mem_map_iff_mem b.injective).mp hmem
    exact False.elim (hwD hh)
  · exact he

omit [Finite F] [CharP F 2] in
private theorem torus_commute (x y : Model F) (hx : x ∈ splitTorus)
    (hy : y ∈ splitTorus) : Commute x y := by
  obtain ⟨⟨l,m⟩,rfl⟩ := hx
  obtain ⟨⟨r,s⟩,rfl⟩ := hy
  change torus l m * torus r s = torus r s * torus l m
  simp only [torus_product,mul_comm]

omit [Finite F] [CharP F 2] in
private theorem scalar_iff (l m : Fˣ) :
    Commute (torus l m) (weylS : Model F) ↔ l=m := by
  rw [Commute, SemiconjBy]
  constructor
  · intro he
    have hh : weylS * torus l m * weylS⁻¹ = torus l m := by
      rw [←he,mul_inv_cancel_right]
    rw [weylS_torus] at hh
    exact (congrArg Prod.fst (torusHom_injective (show torusHom (m,l) = torusHom (l,m) from hh))).symm
  · rintro rfl
    have hh := weylS_torus l l
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm

omit [Finite F] [CharP F 2] in
private theorem scalar_preserved (b : MulAut (parabolic₁ (F := F)))
    (hD : (splitTorus.subgroupOf parabolic₁).map b.toMonoidHom =
      splitTorus.subgroupOf parabolic₁)
    (hS : ∃ l m : Fˣ, (b ⟨weylS,mem_sup_right (subset_closure (by simp))⟩).val =
      torus l m * weylS) (l : Fˣ) :
    ∃ m : Fˣ, (b ⟨torus l l,borel_le_parabolic₁ (mem_sup_right ⟨(l,l),rfl⟩)⟩).val = torus m m := by
  let x : parabolic₁ (F := F) := ⟨torus l l,borel_le_parabolic₁ (mem_sup_right ⟨(l,l),rfl⟩)⟩
  have hx : b x ∈ splitTorus.subgroupOf parabolic₁ := by
    rw [←hD]
    exact mem_map_of_mem _ (show x ∈ splitTorus.subgroupOf parabolic₁ from ⟨(l,l),rfl⟩)
  obtain ⟨⟨r,s⟩,hrs⟩ := hx
  change torus r s = (b x).val at hrs
  obtain ⟨u,v,huv⟩ := hS
  have hc : Commute x (⟨weylS,mem_sup_right (subset_closure (by simp))⟩ : parabolic₁ (F := F)) :=
    Subtype.ext ((scalar_iff l l).mpr rfl).eq
  have hh := congrArg Subtype.val (hc.map b).eq
  change (b x).val * _ = _ * (b x).val at hh
  rw [←hrs,huv] at hh
  have hcd := (torus_commute (torus r s) (torus u v) ⟨(r,s),rfl⟩ ⟨(u,v),rfl⟩).eq
  have hcs : Commute (torus r s) (weylS : Model F) := by
    apply mul_left_cancel (a := torus u v)
    simpa only [←mul_assoc,hcd] using hh
  have hrs' := (scalar_iff r s).mp hcs
  exact ⟨r,hrs.symm.trans (by rw [hrs'])⟩

omit [Finite F] [CharP F 2] in
private theorem root_mem (i : Fin 6) (x : F) :
    RootDiagonal.root ⟨i.val,by omega⟩ x ∈ unipotent (K := F) := by
  fin_cases i <;>
    first
    | exact (fiveRootSubgroup_le_unipotent _ _) (rootA_mem_radical₁ x)
    | simpa [unipotentProduct,RootDiagonal.root] using
        unipotentProduct_mem ![0,x,0,0,0,0]
    | simpa [unipotentProduct,RootDiagonal.root] using
        unipotentProduct_mem ![0,0,x,0,0,0]
    | simpa [unipotentProduct,RootDiagonal.root] using
        unipotentProduct_mem ![0,0,0,x,0,0]
    | simpa [unipotentProduct,RootDiagonal.root] using
        unipotentProduct_mem ![0,0,0,0,x,0]
    | simpa [unipotentProduct,RootDiagonal.root] using
        unipotentProduct_mem ![0,0,0,0,0,x]

private def rootU (i : Fin 6) : Multiplicative F →* unipotent (K := F) :=
  (rootHom ⟨i.val,by omega⟩).codRestrict unipotent (fun x => root_mem i x.toAdd)

private def Preserves (a : MulAut (unipotent (K := F))) (i : Fin 6) : Prop :=
  ∀ x : F, ∃ y : F, a (rootU i (Multiplicative.ofAdd x)) = rootU i (Multiplicative.ofAdd y)

omit [Finite F] in
private theorem preserves_highest (a : MulAut (unipotent (K := F))) : Preserves a 0 := by
  intro x
  have hx : rootU 0 (Multiplicative.ofAdd x) ∈ center (unipotent (K := F)) := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨v,rfl⟩ := unipotentEquiv.surjective y
    exact Subtype.ext (unipotentProduct_commute_rootA v x).eq
  have hy : a (rootU 0 (Multiplicative.ofAdd x)) ∈ center (unipotent (K := F)) := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨z,rfl⟩ := a.surjective y
    simpa only [map_mul] using congrArg a ((mem_center_iff.mp hx) z)
  have hh : (a (rootU 0 (Multiplicative.ofAdd x))).val ∈ highestRoot := by
    rw [←unipotent_center]
    exact mem_map_of_mem unipotent.subtype hy
  obtain ⟨y,hy⟩ := hh
  exact ⟨y.toAdd,Subtype.ext hy.symm⟩

private theorem preserves_short (hq : 2 < Nat.card F)
    (a : MulAut (unipotent (K := F))) (b : MulAut (parabolic₁ (F := F)))
    (hcompat : ∀ x : unipotent (K := F),
      (b ⟨x.val,borel_le_parabolic₁ (mem_sup_left x.property)⟩).val = (a x).val)
    (hD : (splitTorus.subgroupOf parabolic₁).map b.toMonoidHom =
      splitTorus.subgroupOf parabolic₁) : Preserves a 5 := by
  have hS := weyl_image parabolic₁ (le_sup_right.trans borel_le_parabolic₁) b hD
    weylS (mem_sup_right (subset_closure (by simp))) weylS_mem_torusNormalizer
    weylS_not_mem_torus (rankOne_torusNormalizerCover_short hq)
  choose f hf using scalar_preserved b hD hS
  have hfi : Function.Injective f := by
    intro l m he
    have hh : (b ⟨torus l l,borel_le_parabolic₁ (mem_sup_right ⟨(l,l),rfl⟩)⟩).val =
        (b ⟨torus m m,borel_le_parabolic₁ (mem_sup_right ⟨(m,m),rfl⟩)⟩).val := by rw [hf,hf,he]
    exact congrArg Prod.fst (torusHom_injective (show torusHom (l,l) = torusHom (m,m) from congrArg Subtype.val (b.injective (Subtype.ext hh))))
  have hfs := Finite.surjective_of_injective hfi
  intro x
  obtain ⟨y,hy⟩ := scalar_torus_centralizer hq
    (a (rootU 5 (Multiplicative.ofAdd x))).val
    (a (rootU 5 (Multiplicative.ofAdd x))).property (by
      intro l
      obtain ⟨m,rfl⟩ := hfs l
      have hc : Commute (torus m m) (rootF x) := by
        have hh := torus_rootF m m x
        have he : (m:F) * (m:F)⁻¹=1 := mul_inv_cancel₀ (Units.ne_zero m)
        exact mul_inv_eq_iff_eq_mul.mp (by simpa using hh)
      have hp : Commute
          (⟨torus m m,borel_le_parabolic₁ (mem_sup_right ⟨(m,m),rfl⟩)⟩ : parabolic₁ (F := F))
          ⟨rootF x,borel_le_parabolic₁ (mem_sup_left (root_mem 5 x))⟩ := Subtype.ext hc.eq
      have hh := congrArg Subtype.val (hp.map b).eq
      change _ * (b ⟨(rootU 5 (Multiplicative.ofAdd x)).val,_⟩).val =
        (b ⟨(rootU 5 (Multiplicative.ofAdd x)).val,_⟩).val * _ at hh
      rw [hcompat,hf] at hh
      exact hh)
  exact ⟨y,Subtype.ext hy⟩



omit [Finite F] [CharP F 2] in
private theorem preserves_weyl (P : Subgroup (Model F))
    (hUP : unipotent ≤ P) (a : MulAut (unipotent (K := F))) (b : MulAut P)
    (hcompat : ∀ x : unipotent (K := F), (b ⟨x.val,hUP x.property⟩).val = (a x).val)
    (w : Model F) (hwP : w ∈ P)
    (hw : ∃ l m : Fˣ, (b ⟨w,hwP⟩).val = torus l m * w)
    (i j : Fin 6)
    (hij : ∀ x : F, w * (rootU i (Multiplicative.ofAdd x)).val * w⁻¹ =
      (rootU j (Multiplicative.ofAdd x)).val)
    (hi : Preserves a i) : Preserves a j := by
  intro x
  obtain ⟨y,hy⟩ := hi x
  obtain ⟨l,m,hlm⟩ := hw
  have hb : (⟨(rootU j (Multiplicative.ofAdd x)).val,hUP (root_mem j x)⟩ : P) =
      ⟨w,hwP⟩ * ⟨(rootU i (Multiplicative.ofAdd x)).val,hUP (root_mem i x)⟩ * ⟨w,hwP⟩⁻¹ :=
    Subtype.ext (hij x).symm
  have he : (a (rootU j (Multiplicative.ofAdd x))).val =
      torus l m * (rootU j (Multiplicative.ofAdd y)).val * (torus l m)⁻¹ := by
    rw [←hcompat,hb,map_mul,map_mul,map_inv]
    change (b ⟨w,hwP⟩).val * (b ⟨(rootU i (Multiplicative.ofAdd x)).val,_⟩).val *
      (b ⟨w,hwP⟩).val⁻¹ = _
    rw [hlm,hcompat,hy,←hij y]
    group
  obtain ⟨u,v,hc⟩ := RootDiagonal.diagonal_iff_torus (MulAut.conj (torus l m : Model F)) |>.mpr
    ⟨torus l m,⟨(l,m),rfl⟩,rfl⟩
  refine ⟨(RootDiagonal.character u v ⟨j.val,by omega⟩ : F)*y,Subtype.ext ?_⟩
  exact he.trans (hc ⟨j.val,by omega⟩ y)

private theorem all_preserved (hq : 2 < Nat.card F)
    (a : MulAut (unipotent (K := F)))
    (b : MulAut (parabolic₁ (F := F))) (c : MulAut (parabolic₂ (F := F)))
    (hb : ∀ x : unipotent (K := F),
      (b ⟨x.val,borel_le_parabolic₁ (mem_sup_left x.property)⟩).val = (a x).val)
    (hc : ∀ x : unipotent (K := F),
      (c ⟨x.val,borel_le_parabolic₂ (mem_sup_left x.property)⟩).val = (a x).val)
    (hbD : (splitTorus.subgroupOf parabolic₁).map b.toMonoidHom = splitTorus.subgroupOf parabolic₁)
    (hcD : (splitTorus.subgroupOf parabolic₂).map c.toMonoidHom = splitTorus.subgroupOf parabolic₂) :
    ∀ i : Fin 6, Preserves a i := by
  have hs := weyl_image parabolic₁ (le_sup_right.trans borel_le_parabolic₁) b hbD
    weylS (mem_sup_right (subset_closure (by simp))) weylS_mem_torusNormalizer
    weylS_not_mem_torus (rankOne_torusNormalizerCover_short hq)
  have hr := weyl_image parabolic₂ (le_sup_right.trans borel_le_parabolic₂) c hcD
    weylR (mem_sup_right (subset_closure (by simp))) weylR_mem_torusNormalizer
    weylR_not_mem_torus (rankOne_torusNormalizerCover_long hq)
  have hA := preserves_highest a
  have hF := preserves_short hq a b hb hbD
  have hB := preserves_weyl parabolic₂ (le_sup_left.trans borel_le_parabolic₂) a c hc
    weylR _ hr 0 1 (fun x => weylR_rootA x) hA
  have hE := preserves_weyl parabolic₁ (le_sup_left.trans borel_le_parabolic₁) a b hb
    weylS _ hs 1 4 (fun x => weylS_rootB x) hB
  have hD := preserves_weyl parabolic₂ (le_sup_left.trans borel_le_parabolic₂) a c hc
    weylR _ hr 5 3 (fun x => by
      change weylR * rootF x * weylR⁻¹ = rootD x
      rw [←weylR_rootD]
      have hh : (weylR : Model F)*weylR=1 := by rw [←pow_two,weylR_sq]
      calc
        _ = (weylR*weylR)*rootD x*(weylR*weylR)⁻¹ := by group
        _ = rootD x := by rw [hh]; simp) hF
  have hC := preserves_weyl parabolic₁ (le_sup_left.trans borel_le_parabolic₁) a b hb
    weylS _ hs 3 2 (fun x => weylS_rootD x) hD
  intro i
  fin_cases i <;> assumption

omit [Finite F] [CharP F 2] in
private theorem rootU_injective (i : Fin 6) : Function.Injective (rootU (F := F) i) := by
  intro x y hh
  exact Multiplicative.toAdd.injective
    (root_injective ⟨i.val,by omega⟩ (congrArg Subtype.val hh))

omit [CharP F 2] in
private theorem root_parameter (a : MulAut (unipotent (K := F)))
    (i : Fin 6) (h : Preserves a i) :
    ∃ ρ : F ≃+ F, ∀ x, a (rootU i (Multiplicative.ofAdd x)) = rootU i (Multiplicative.ofAdd (ρ x)) := by
  choose f hf using h
  have hfi : Function.Injective f := by
    intro x y he
    apply Multiplicative.ofAdd.injective
    apply rootU_injective i
    apply a.injective
    rw [hf,hf,he]
  have hadd (x y : F) : f (x+y)=f x+f y := by
    apply Multiplicative.ofAdd.injective
    apply rootU_injective i
    change rootU i (Multiplicative.ofAdd (f (x+y))) =
      rootU i (Multiplicative.ofAdd (f x) * Multiplicative.ofAdd (f y))
    rw [map_mul,←hf (x+y),←hf x,←hf y,←map_mul]
    congr 1
    exact (rootU i).map_mul (Multiplicative.ofAdd x) (Multiplicative.ofAdd y)
  let fhom : F →+ F :=
    { toFun := f
      map_zero' := by
        have hh : f 0 + 0 = f 0 + f 0 := by simpa only [add_zero] using hadd 0 0
        exact (add_left_cancel hh).symm
      map_add' := hadd }
  let ρ : F ≃+ F := AddEquiv.ofBijective fhom ⟨hfi,Finite.surjective_of_injective hfi⟩
  exact ⟨ρ,hf⟩

omit [CharP F 2] in
private theorem parameters (a : MulAut (unipotent (K := F)))
    (hpres : ∀ i : Fin 6, Preserves a i) :
    ∃ ρ : Fin 6 → F ≃+ F, ∀ v : Fin 6 → F,
      (a (unipotentEquiv v)).val = unipotentProduct (fun i => ρ i (v i)) := by
  choose ρ hroot using fun i => root_parameter a i (hpres i)
  refine ⟨ρ,?_⟩
  intro v
  have he : unipotentEquiv v = rootU 0 (Multiplicative.ofAdd (v 0)) *
      rootU 1 (Multiplicative.ofAdd (v 1)) * rootU 2 (Multiplicative.ofAdd (v 2)) *
      rootU 3 (Multiplicative.ofAdd (v 3)) * rootU 4 (Multiplicative.ofAdd (v 4)) *
      rootU 5 (Multiplicative.ofAdd (v 5)) := Subtype.ext rfl
  rw [he,map_mul,map_mul,map_mul,map_mul,map_mul,hroot,hroot,hroot,hroot,hroot,hroot]
  rfl

/-- Compatible actions on the two marked parabolics preserving their common
split torus preserve each of the six positive root groups, including over F₄. -/
theorem root_actions (hq : 2 < Nat.card F)
    (a : MulAut (unipotent (K := F)))
    (b : MulAut (parabolic₁ (F := F))) (c : MulAut (parabolic₂ (F := F)))
    (hb : ∀ x : unipotent (K := F),
      (b ⟨x.val,borel_le_parabolic₁ (mem_sup_left x.property)⟩).val = (a x).val)
    (hc : ∀ x : unipotent (K := F),
      (c ⟨x.val,borel_le_parabolic₂ (mem_sup_left x.property)⟩).val = (a x).val)
    (hbD : (splitTorus.subgroupOf parabolic₁).map b.toMonoidHom = splitTorus.subgroupOf parabolic₁)
    (hcD : (splitTorus.subgroupOf parabolic₂).map c.toMonoidHom = splitTorus.subgroupOf parabolic₂) :
    ∃ ρ : Fin 6 → F ≃+ F, ∀ v : Fin 6 → F,
      (a (unipotentEquiv v)).val = unipotentProduct (fun i => ρ i (v i)) := by
  exact parameters a (all_preserved hq a b c hb hc hbD hcD)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.G2OuterRootNormalization
