module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.OppositeCore.NaturalQuotient.Recognition
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.CartanGeometry.Torus

/-!
# The full original Cartan on the selected opposite plane

The two Borel characters identify the source Cartan with the full split
rank-two torus. Equal characters kill the middle SL₂ block: it is both
unipotent and of odd order. Opposite-point invariance then kills the point
radical, giving every scalar diagonal on the first hyperbolic plane.
These lifts centralize the literal L₁/O₂(L₁), hence belong to X₁. Their
original pair marking supplies a nonidentity diagonal on Q/((W∩Wʸ)V),
discharging the natural-quotient fixed-point bound, including q=4.

The converse scalar criterion retains the same quotient and both points;
it is used for conjugacy under the full opposite-point stabilizer.
Source: Aschbacher--Smith 11.5.7, printed p.783.
-/

open Subgroup Matrix
open scoped MatrixGroups
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
set_option backward.isDefEq.respectTransparency false
open scoped Pointwise
public noncomputable section

private theorem odd_two_kernel_injective {A B : Type*} [Group A] [Group B] [Finite A]
    (f : A →* B) (ho : Odd (Nat.card A)) (hk : IsPGroup 2 f.ker) :
    Function.Injective f := by
  apply (MonoidHom.ker_eq_bot_iff f).mp
  apply card_eq_one.mp
  exact hk.card_eq_or_dvd.resolve_right
    (fun h => ho.not_two_dvd_nat (h.trans (card_subgroup_dvd_card _)))

private theorem scalar_of_equal_characters {F : Type*} [Field F] [CharP F 2]
    (b : borel (F := F)) (s : Fˣ) (hc : borelCharacters b = (s,s))
    (ho : Odd (orderOf b))
    (hp : b.val ∈ stabilizer (F ∙ (Pi.single (.inr 0) 1 : Vector F))) :
    b.val = diagonalTorus s 1 := by
  let q := pointParabolicQuotient (inclusion (show borel (F := F) ≤ pointParabolic from inf_le_left) b)
  have hb := (mem_borel_iff b.val).mp b.property
  have h00 : b.val.val (.inl 0) (.inl 0) = (s:F) := by
    rw [← determinantCharacter_point_coe ⟨b.val,b.property.1⟩]
    exact congrArg (fun z : Fˣ × Fˣ => (z.1:F)) hc
  have hdet : (Plane.upperLeft ⟨b.val,b.property.2⟩).det = (s:F) := by
    rw [Plane.upperLeft_det]
    exact congrArg (fun z : Fˣ × Fˣ => (z.2:F)) hc
  have h11 : b.val.val (.inl 1) (.inl 1) = 1 := by
    rw [det_fin_two] at hdet
    change b.val.val (.inl 0) (.inl 0) * b.val.val (.inl 1) (.inl 1) -
      b.val.val (.inl 0) (.inl 1) * b.val.val (.inl 1) (.inl 0) = (s:F) at hdet
    rw [h00,hb.1,mul_zero,sub_zero] at hdet
    exact (mul_eq_left₀ s.ne_zero).mp hdet
  have hq00 : q.val 0 0 = 1 := h11
  have hq10 : q.val 1 0 = 0 := hb.2 1 1
  have hq11 : q.val 1 1 = 1 := by
    simpa only [det_fin_two,hq00,hq10,one_mul,mul_zero,sub_zero] using q.property
  have hq2 : q^2 = 1 := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_two, mul_apply,Fin.sum_univ_two,hq00,hq10,hq11,CharTwo.add_self_eq_zero]
  have hqo : Odd (orderOf q) := ho.of_dvd_nat
    (orderOf_map_dvd ((pointParabolicQuotient (F := F)).comp (inclusion inf_le_left)) b)
  have hq1 : q = 1 := by
    apply orderOf_eq_one_iff.mp
    exact Nat.eq_one_of_dvd_coprimes hqo.coprime_two_right (dvd_refl _) (orderOf_dvd_of_pow_eq_one hq2)
  obtain ⟨t,ht⟩ := OppositeLongRootPair.scalar_of_quotient_eq_one
    ⟨b.val,b.property.1⟩ hq1 hp
  have hts : t = s := by
    apply Units.ext
    rw [ht] at h00
    simpa [diagonalTorus,Matrix.diagonal] using h00
  simpa [hts] using ht

private theorem unmove_stabilizer {F : Type*} [Field F]
    (U : Submodule F (Vector F)) (g x : Sp F)
    (hx : x ∈ stabilizer (U.map (toLinear g).toLinearMap)) :
    g⁻¹ * x * g ∈ stabilizer U := by
  apply (mem_stabilizer_iff _ _).mpr
  intro v hv
  obtain ⟨w,hw,he⟩ := (mem_stabilizer_iff _ _).mp hx (g • v) ⟨v,hv,rfl⟩
  have he' : g⁻¹ • (x • (g • v)) = w := by
    rw [← show g • w = x • (g • v) from he,inv_smul_smul]
  change (g⁻¹ * x * g) • v ∈ U
  rw [mul_smul,mul_smul,he']
  exact hw

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.NaturalQuotient
open CFSG.Quasithin.Chapter12.Section02 OppositeGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

private theorem model_stabilizer_of_normalizes (m : MarkedFlag E)
    (U : Submodule E.input.field.Carrier (Vector E.input.field.Carrier)) (x : L)
    (hn : (x : G) ∈ normalizer ((LocalGeometry.Coordinates.sp4 m.action).preimage U : Set G)) :
    PointModel.quotientMap m x ∈ stabilizer U := by
  apply (mem_stabilizer_iff _ _).mpr
  intro v hv
  exact (((LocalGeometry.Coordinates.sp4 m.action).mem_normalizer_preimage_iff U x).mp hn v).mpr hv

/-- Each scalar on the first hyperbolic plane has a lift in the original Cartan. -/
theorem exists_cartan_scalar_lift (m : MarkedFlag E)
    (hX : LocalGeometry.IsCartan T L E.X) (g : Sp E.input.field.Carrier)
    (hflag : ∀ i : Fin 3, m.flag.space i = LocalGeometry.Sp4.ModelFlag.movedStage g i.succ)
    (y : L) (hy : PointModel.quotientMap m y = g * TwoConjugate.opposition * g⁻¹)
    (hXpoint : E.X ≤ normalizer (E.V₁.map (MulAut.conj (y:G)).toMonoidHom : Set G))
    (s : E.input.field.Carrierˣ) :
    ∃ x : E.X, PointModel.quotientMap m (inclusion (hX.1.trans inf_le_left) x) =
      g * diagonalTorus s 1 * g⁻¹ := by
  let hXL : E.X ≤ L := hX.1.trans inf_le_left
  let q : E.X →* Sp E.input.field.Carrier := (PointModel.quotientMap m).comp (inclusion hXL)
  have hq : Function.Injective q := by
    apply odd_two_kernel_injective q hX.odd
    rw [show q.ker = (PointModel.quotientMap m).ker.comap (inclusion hXL) from rfl,
      PointModel.quotientMap_ker]
    exact (pCore_isPGroup (p := 2) (G := L)).comap_of_injective _ (inclusion_injective hXL)
  let f : E.X →* Sp E.input.field.Carrier := (MulAut.conj g⁻¹).toMonoidHom.comp q
  have hf : Function.Injective f := (MulAut.conj g⁻¹).injective.comp hq
  have hb (x : E.X) : f x ∈ Theory.SpecificGroups.SymplecticFour.borel := by
    have hs (i : Fin 3) : f x ∈ stabilizer (LocalGeometry.Sp4.ModelFlag.stage i.succ) := by
      dsimp only [f,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.conj_apply]
      rw [inv_inv]
      apply unmove_stabilizer _ g (q x)
      have hh := model_stabilizer_of_normalizes E m (m.flag.space i) (inclusion hXL x)
        (cartan_normalizes_marked_flag E m hX i x.property)
      rwa [hflag] at hh
    exact ⟨hs 0,hs 1⟩
  let fb : E.X →* Theory.SpecificGroups.SymplecticFour.borel (F := E.input.field.Carrier) := f.codRestrict _ hb
  let c := borelCharacters.comp fb
  have hci : Function.Injective c := by
    apply odd_two_kernel_injective c hX.odd
    have he : c.ker = unipotent.comap f := by
      ext x
      exact borelCharacters_eq_one (fb x)
    rw [he]
    exact (isPGroup_unipotent E.input.field.card_eq).comap_of_injective f hf
  have hcs : Function.Surjective c := (hci.bijective_of_nat_card_le (by
    rw [Nat.card_prod,Nat.card_units,E.input.field.card_eq,
      (LocalGeometry.Coordinates.sp4 m.action).cartan_card hX,pow_two])).2
  obtain ⟨x,hx⟩ := hcs (s,s)
  have ho : Odd (orderOf (fb x)) :=
    hX.odd.of_dvd_nat ((orderOf_map_dvd fb x).trans (orderOf_dvd_natCard x))
  have hp : f x ∈ stabilizer (E.input.field.Carrier ∙
      (Pi.single (.inr 0) 1 : Vector E.input.field.Carrier)) := by
    dsimp only [f,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.conj_apply]
    rw [inv_inv]
    apply unmove_stabilizer _ g (q x)
    apply model_stabilizer_of_normalizes E m _ (inclusion hXL x)
    rw [← opposition_point_preimage E m g (hflag 0) y hy]
    exact hXpoint x.property
  have he := scalar_of_equal_characters (fb x) s hx ho hp
  refine ⟨x,?_⟩
  change g⁻¹ * q x * (g⁻¹)⁻¹ = diagonalTorus s 1 at he
  have hh := congrArg (fun z => g*z*g⁻¹) he
  simpa only [inv_inv,mul_assoc,mul_inv_cancel_left,mul_inv_cancel,mul_one,q,
    MonoidHom.comp_apply] using hh

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.NaturalQuotient

open scoped commutatorElement
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure
variable {G : Type*} [Group G]
private theorem coreQuotientCentralizer_of_commutators {K : Subgroup G} {x : G}
    (hn : x ∈ normalizer (K : Set G))
    (hc : ∀ k ∈ K, ⁅x,k⁆ ∈ K.pCoreIn 2) :
    x ∈ coreQuotientCentralizer K := by
  refine ⟨⟨x,hn⟩,?_,rfl⟩
  apply MulEquiv.ext
  intro q
  obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) q
  rw [coreQuotientAction_apply_mk]
  obtain ⟨c,hc,he⟩ := hc k k.property
  have he' : c = K.normalizerMonoidHom ⟨x,hn⟩ k * k⁻¹ := Subtype.ext he
  have hh := (QuotientGroup.eq_one_iff (N := pCore 2 K)
    (K.normalizerMonoidHom ⟨x,hn⟩ k * k⁻¹)).mpr (he' ▸ hc)
  change QuotientGroup.mk' (pCore 2 K)
    (K.normalizerMonoidHom ⟨x,hn⟩ k * k⁻¹) = 1 at hh
  rw [map_mul,map_inv] at hh
  exact mul_inv_eq_one.mp hh

open CFSG.Quasithin.Chapter12.Section02 Symplectic
variable [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {E : Geometry D} (m : MarkedFlag E)
private theorem local_core_of_image_mem (a : L) (ha : (a:G) ∈ E.L₁)
    (h : PointModel.quotientMap m a ∈ (PointModel.image m E.L₁).pCoreIn 2) :
    (a:G) ∈ E.L₁.pCoreIn 2 := by
  rw [← PointModel.image_core m E.L₁ E.L₁_le] at h
  obtain ⟨c,hc,he⟩ := h
  have hca : c⁻¹*a ∈ pCore 2 L := by
    rw [← PointModel.quotientMap_ker m]
    change PointModel.quotientMap m (c⁻¹*a) = 1
    rw [map_mul,map_inv,he,inv_mul_cancel]
  have hd : (c:G)⁻¹*(a:G) ∈ E.L₁.pCoreIn 2 :=
    inf_pCoreIn_le_of_le 2 E.L₁_le
      ⟨E.L₁.mul_mem (E.L₁.inv_mem (pCoreIn_le 2 E.L₁ hc)) ha,
        mem_map_of_mem L.subtype hca⟩
  have hh : (c:G) * ((c:G)⁻¹ * (a:G)) ∈ E.L₁.pCoreIn 2 :=
    (E.L₁.pCoreIn 2).mul_mem hc hd
  simpa only [mul_inv_cancel_left] using hh

namespace Symplectic.NaturalQuotient
open OppositeGeometry
variable (E)
private theorem scalar_commutators {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1<n) (s : Fˣ) :
    ∀ l ∈ pointLocal (F := F), ⁅diagonalTorus s 1,l⁆ ∈ pointLocal.pCoreIn 2 := by
  intro l hl
  have hnL : diagonalTorus s 1 ∈ normalizer (pointLocal (F := F) : Set _) := by
    rw [DiagramAutomorphisms.pointLocal_normalizer hF hn]
    exact (diagonalTorus_mem_borel s 1).1
  have hlc : ⁅diagonalTorus s 1,l⁆ ∈ pointLocal :=
    (pointLocal (F := F)).mul_mem ((mem_normalizer_iff.mp hnL l).mp hl)
      ((pointLocal (F := F)).inv_mem hl)
  have hh := (mem_coreCenterIn_iff 2 pointParabolic _).mp
    (RootCoreTori.point_scalar_mem_coreCenter hF hn s)
  exact inf_pCoreIn_le_of_le 2 pointLocal_le ⟨hlc,hh.2 l (pointLocal_le hl)⟩

theorem scalar_lift_mem_cartanKernel (hX : LocalGeometry.IsCartan T L E.X)
    (g : Sp E.input.field.Carrier)
    (hlocal : PointModel.image m E.L₁ = pointLocal.map (MulAut.conj g).toMonoidHom)
    (x : E.X) (s : E.input.field.Carrierˣ)
    (hx : PointModel.quotientMap m (inclusion (hX.1.trans inf_le_left) x) =
      g * diagonalTorus s 1 * g⁻¹) : (x:G) ∈ cartanKernel E := by
  have hXG : E.X ≤ E.G₁ := by
    change E.X ≤ normalizer (E.V₁ : Set G)
    rw [m.point_preimage]
    exact cartan_normalizes_marked_flag E m hX 0
  have hn : E.X ≤ normalizer (E.L₁ : Set G) := by
    apply le_trans _ (normalizer_le_normalizer_characteristic_image
      (L ⊓ E.G₁) (solvableResidual (L ⊓ E.G₁ : Subgroup G)))
    exact (le_inf ((hX.1.trans inf_le_left).trans L.le_normalizer)
      (hXG.trans E.G₁.le_normalizer)).trans inf_normalizer_le_normalizer_inf
  refine ⟨x.property,coreQuotientCentralizer_of_commutators (hn x.property) ?_⟩
  intro l hl
  let z : L := inclusion (hX.1.trans inf_le_left) x
  let k : L := ⟨l,E.L₁_le hl⟩
  apply local_core_of_image_mem m ⁅z,k⁆ (E.L₁.mul_mem ((mem_normalizer_iff.mp (hn x.property) l).mp hl) (E.L₁.inv_mem hl))
  rw [map_commutatorElement,hx,hlocal]
  have hk : PointModel.quotientMap m k ∈ pointLocal.map (MulAut.conj g).toMonoidHom := by
    rw [← hlocal]
    exact mem_map_of_mem _ hl
  obtain ⟨a,ha,he⟩ := hk
  rw [← he,← map_pCoreIn_of_injective 2 _ _ (MulAut.conj g).injective]
  have hh := mem_map_of_mem (MulAut.conj g).toMonoidHom
    (scalar_commutators E.input.field.card_eq E.input.nonbinary s a ha)
  rwa [map_commutatorElement] at hh

end Symplectic.NaturalQuotient
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.NaturalQuotient
open CFSG.Quasithin.Chapter12.Section02 OppositeGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- The original pair marking agrees with the original component marking. -/
theorem pairAction_component (m : MarkedFlag E) (hW : E.W ≤ E.G₁.pCoreIn 2)
    (g : Sp E.input.field.Carrier) (y : L)
    (hi : actionImage (V := V) (oppositeJoin (auxiliaryW E) (y:G)) =
      (OppositeLongRootPair.pair.map (MulAut.conj g).toMonoidHom).map (FullAction.modelHom m))
    (x : L) (hx : (x:G) ∈ oppositeJoin (auxiliaryW E) (y:G)) :
    g * OppositeLongRootPair.embedding (pairAction E m hW g y hi ⟨x,hx⟩) * g⁻¹ =
      PointModel.quotientMap m x := by
  apply FullAction.modelHom_injective m
  rw [FullAction.modelHom_quotientMap]
  exact pairAction_spec E m hW g y hi ⟨x,hx⟩

private theorem embedding_diagonal {F : Type*} [Field F] (s : Fˣ) :
    OppositeLongRootPair.embedding
      (⟨Matrix.diagonal ![(s:F),(↑s⁻¹:F)],by simp⟩ : SL(2,F)) = diagonalTorus s 1 := by
  apply Subtype.ext
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [OppositeLongRootPair.embedding,OppositeLongRootPair.matrix,diagonalTorus,Matrix.diagonal]

/-- Every nonidentity scalar is realized in X₁ for the same pair marking. -/
theorem exists_marked_cartan_diagonal (m : MarkedFlag E)
    (hX : LocalGeometry.IsCartan T L E.X) (hW : E.W ≤ E.G₁.pCoreIn 2)
    (g : Sp E.input.field.Carrier)
    (hflag : ∀ i : Fin 3, m.flag.space i = LocalGeometry.Sp4.ModelFlag.movedStage g i.succ)
    (y : L) (hy : PointModel.quotientMap m y = g * TwoConjugate.opposition * g⁻¹)
    (hXpoint : E.X ≤ normalizer (E.V₁.map (MulAut.conj (y:G)).toMonoidHom : Set G))
    (hi : actionImage (V := V) (oppositeJoin (auxiliaryW E) (y:G)) =
      (OppositeLongRootPair.pair.map (MulAut.conj g).toMonoidHom).map (FullAction.modelHom m))
    (hXI : cartanKernel E ≤ oppositeJoin (auxiliaryW E) (y:G))
    (s : E.input.field.Carrierˣ) :
    ∃ (x : G) (hx : x ∈ cartanKernel E),
      (pairAction E m hW g y hi ⟨x,hXI hx⟩).val = Matrix.diagonal ![(s:E.input.field.Carrier),(↑s⁻¹:E.input.field.Carrier)] := by
  obtain ⟨x,hx⟩ := exists_cartan_scalar_lift E m hX g hflag y hy hXpoint s
  have hxX := scalar_lift_mem_cartanKernel E m hX g
    (PointModel.local_identification m g (hflag 0)) x s hx
  refine ⟨x,hxX,?_⟩
  let z : L := inclusion (hX.1.trans inf_le_left) x
  have he := (pairAction_component E m hW g y hi z (hXI hxX)).trans hx
  have he' : OppositeLongRootPair.embedding (pairAction E m hW g y hi ⟨x,hXI hxX⟩) =
      diagonalTorus s 1 := (MulAut.conj g).injective he
  rw [← embedding_diagonal] at he'
  exact congrArg Subtype.val (OppositeLongRootPair.embedding_injective he')

/-- The Cartan fixed-space bound has no remaining diagonal or natural-module premise. -/
theorem centralizer_le_of_cartan_opposite (m : MarkedFlag E)
    (hX : LocalGeometry.IsCartan T L E.X) (hW : E.W ≤ E.G₁.pCoreIn 2)
    (hPhi : (frattini (auxiliaryW E)).map (auxiliaryW E).subtype ≤ E.V₁)
    (g : Sp E.input.field.Carrier)
    (hflag : ∀ i : Fin 3, m.flag.space i = LocalGeometry.Sp4.ModelFlag.movedStage g i.succ)
    (y : L) (hy : PointModel.quotientMap m y = g * TwoConjugate.opposition * g⁻¹)
    (hXpoint : E.X ≤ normalizer (E.V₁.map (MulAut.conj (y:G)).toMonoidHom : Set G))
    (hi : actionImage (V := V) (oppositeJoin (auxiliaryW E) (y:G)) =
      (OppositeLongRootPair.pair.map (MulAut.conj g).toMonoidHom).map (FullAction.modelHom m))
    (hroot : actionImage (V := V) (auxiliaryW E) =
      ((RootSubgroup.group 0).map (MulAut.conj g).toMonoidHom).map (FullAction.modelHom m))
    (hmove : ⁅V,auxiliaryW E⁆ = E.V₁)
    (hsplit : V = E.V₃ ⊔ E.V₁.map (MulAut.conj (y:G)).toMonoidHom)
    (hcore : (oppositeJoin (auxiliaryW E) (y:G)).pCoreIn 2 ≤ (L ⊔ (T:Subgroup G)).pCoreIn 2)
    (hXI : cartanKernel E ≤ oppositeJoin (auxiliaryW E) (y:G)) :
    corePair (auxiliaryW E) (y:G) ⊓ centralizer (cartanKernel E : Set G) ≤ pairDenominator E (y:G) := by
  have hc : 1 < Nat.card E.input.field.Carrierˣ := by
    rw [Nat.card_units,E.input.field.card_eq]
    have hp : 2^2 ≤ 2^E.input.field.degree := Nat.pow_le_pow_right (by decide) E.input.nonbinary
    omega
  have : Nontrivial E.input.field.Carrierˣ := Finite.one_lt_card_iff_nontrivial.mp hc
  obtain ⟨s,hs⟩ := exists_ne (1 : E.input.field.Carrierˣ)
  obtain ⟨x,hx,hd⟩ := exists_marked_cartan_diagonal E m hX hW g hflag y hy hXpoint hi hXI s
  exact centralizer_le_of_marked_pair_diagonal E m hW hPhi g (hflag 0) y hy hi hroot hmove hsplit hcore hXI
    x hx (s:E.input.field.Carrier) (fun h => hs (Units.ext h)) (by simpa using hd)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.NaturalQuotient

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.NaturalQuotient
open CFSG.Quasithin.Chapter12.Section02 OppositeGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- In the original quotient, preserving both marked points and centralizing
L₁/O₂(L₁) forces precisely the scalar on the first hyperbolic plane. -/
theorem scalar_image_of_point_pair_centralizer (m : MarkedFlag E)
    (g : Sp E.input.field.Carrier)
    (hpoint : m.flag.space 0 = LocalGeometry.Sp4.ModelFlag.movedStage g 1)
    (y : L) (hy : PointModel.quotientMap m y = g * TwoConjugate.opposition * g⁻¹)
    (x : L) (hp : (x:G) ∈ E.G₁)
    (ho : (x:G) ∈ normalizer (E.V₁.map (MulAut.conj (y:G)).toMonoidHom : Set G))
    (hc : (x:G) ∈ coreQuotientCentralizer E.L₁) :
    ∃ s : E.input.field.Carrierˣ,
      PointModel.quotientMap m x = g * diagonalTorus s 1 * g⁻¹ := by
  let a := PointModel.quotientMap m x
  have hap : g⁻¹*a*g ∈ pointParabolic := by
    apply unmove_stabilizer
    have hh := model_stabilizer_of_normalizes E m (m.flag.space 0) x (by
      change (x:G) ∈ normalizer (m.flag.Vi 0 : Set G)
      rw [← m.point_preimage]; exact hp)
    rwa [hpoint] at hh
  have hao : g⁻¹*a*g ∈ stabilizer (E.input.field.Carrier ∙
      (Pi.single (.inr 0) 1 : Vector E.input.field.Carrier)) := by
    apply unmove_stabilizer
    apply model_stabilizer_of_normalizes E m _ x
    rw [← opposition_point_preimage E m g hpoint y hy]
    exact ho
  have hlocal := PointModel.local_identification m g hpoint
  have hcomm : ∀ l ∈ pointLocal (F := E.input.field.Carrier),
      ⁅g⁻¹*a*g,l⁆ ∈ pointLocal.pCoreIn 2 := by
    intro l hl
    have hm : (MulAut.conj g) l ∈ PointModel.image m E.L₁ := by
      rw [hlocal]
      exact mem_map_of_mem _ hl
    obtain ⟨k,hk,he⟩ := hm
    have hh := mem_map_of_mem (PointModel.quotientMap m)
      (show ⁅x,k⁆ ∈ (E.L₁.pCoreIn 2).subgroupOf L from
        coreQuotientCentralizer_commutator hc hk)
    change PointModel.quotientMap m ⁅x,k⁆ ∈ PointModel.image m (E.L₁.pCoreIn 2) at hh
    rw [map_commutatorElement,he,PointModel.image_core m E.L₁ E.L₁_le,hlocal,
      ← map_pCoreIn_of_injective 2 _ _ (MulAut.conj g).injective] at hh
    obtain ⟨z,hz,hze⟩ := hh
    have hce : (MulAut.conj g) ⁅g⁻¹*a*g,l⁆ = ⁅a,(MulAut.conj g) l⁆ := by
      rw [map_commutatorElement]
      simp [MulAut.conj_apply,mul_assoc]
    have hh' : z = ⁅g⁻¹*a*g,l⁆ := (MulAut.conj g).injective (hze.trans hce.symm)
    rwa [← hh']
  obtain ⟨s,hs⟩ := OppositeLongRootPair.scalar_of_quotient_eq_one ⟨g⁻¹*a*g,hap⟩
    (OppositeLongRootPair.quotient_eq_one_of_commutators E.input.field.card_eq E.input.nonbinary
      ⟨g⁻¹*a*g,hap⟩ hcomm) hao
  refine ⟨s,?_⟩
  have hh := congrArg (fun z => g*z*g⁻¹) hs
  simpa only [mul_assoc,mul_inv_cancel_left,mul_inv_cancel,mul_one] using hh

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.NaturalQuotient

