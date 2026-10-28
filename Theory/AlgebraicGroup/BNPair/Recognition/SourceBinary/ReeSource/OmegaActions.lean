module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.SuzukiBarAction
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.SuzukiRankOne
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.OctagonRoots
public import Theory.SpecificGroups.Suzuki.OmegaGeneration

/-!
# Cartan transitivity and generation on the actual Suzuki Omega roots

The first root coordinate determines its square. Thus the regular action
on the barred root carries any nonidentity square to any other one. Every
Omega element is a square, giving transitivity on the actual Omega subgroup,
including the cyclic root of Sz(2). Right conjugation transports this action
to every shifted root, with the full source Cartan and representatives retained.

For positive parameters, transport the native Omega-and-outside-element
Suzuki generation theorem through the literal faithful endpoint projection.
The actual source reflection is outside the marked Borel. Consequently
normalization of the perpendicular root by Omega forces normalization by the
whole source rank-one group. The separate binary quintic argument is unchanged.

Source: Fong--Seitz I (1973), the nonzero (6.4) upgrade and generation step
in the proof of (6H)(b), printed p.53. ReeSource.OmegaNonzero applies both
results on the same marked quotient; it retains the unresolved Omega movement
alternative and does not claim the final unconditional commutator equality.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) (i : Fin 2) (m : ℕ)
  (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q i).map μ.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))

private theorem square_eq_of_firstCoordinate_eq
    (x y : simpleRoot Q split i)
    (h : suzukiFirstCoordinate Q split i m μ hB x =
      suzukiFirstCoordinate Q split i m μ hB y) : x^2 = y^2 := by
  obtain ⟨⟨a,b⟩,rfl⟩ := (suzukiParameter_bijective Q split i m μ hB).surjective x
  obtain ⟨⟨c,d⟩,rfl⟩ := (suzukiParameter_bijective Q split i m μ hB).surjective y
  simp only [suzukiFirstCoordinate_parameter] at h
  have h' := Multiplicative.ofAdd.injective h
  rw [suzukiParameter_square,suzukiParameter_square,h']

include μ hB in
/-- The full source Cartan is transitive on nonidentity Omega elements, also at q=2. -/
theorem suzuki_omega_cartan_transitive
    (a b : X ⧸ Q.D) (ha : a ∈ omegaOneAmbient (simpleRoot Q split i))
    (hb : b ∈ omegaOneAmbient (simpleRoot Q split i)) (han : a ≠ 1) (hbn : b ≠ 1) :
    ∃ h : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)), (h : X ⧸ Q.D)*a*(h : X ⧸ Q.D)⁻¹ = b := by
  obtain ⟨x,hx,hxa⟩ := (suzukiOmega_mem_iff_square Q split i m μ hB a).mp ha
  obtain ⟨y,hy,hyb⟩ := (suzukiOmega_mem_iff_square Q split i m μ hB b).mp hb
  let x' : simpleRoot Q split i := ⟨x,hx⟩
  let y' : simpleRoot Q split i := ⟨y,hy⟩
  let f := suzukiFirstCoordinate Q split i m μ hB
  have hfx : f x' ≠ 1 := by
    intro hz
    have he := square_eq_of_firstCoordinate_eq Q split i m μ hB x' 1 (hz.trans (map_one f).symm)
    have he' : x^2 = 1 := congrArg Subtype.val (by simpa using he)
    exact han (hxa.symm.trans he')
  have hfy : f y' ≠ 1 := by
    intro hz
    have he := square_eq_of_firstCoordinate_eq Q split i m μ hB y' 1 (hz.trans (map_one f).symm)
    have he' : y^2 = 1 := congrArg Subtype.val (by simpa using he)
    exact hbn (hyb.symm.trans he')
  let ρ := suzukiBarCartanAction Q split i m μ hB
  let : IsCyclic ρ.range := suzukiBarCartanAction_cyclic Q split i m μ hB
    (UnitarySource.actorReflection Q split i)
  let : IsElementaryAbelian 2 (Multiplicative (BinaryGaloisField (2*m+1))) := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
      change 2 • x.toAdd = 0
      exact (two_nsmul _).trans (CharTwo.add_self_eq_zero _)) }
  obtain ⟨c,hc,_⟩ := RootAction.regular_of_card ρ.range.subtype ρ.range.subtype_injective
    (by omega : 0 < 2*m+1)
    (suzukiBarCartanAction_card Q split i m μ hB (UnitarySource.actorReflection Q split i))
    (by rw [Nat.card_congr Multiplicative.ofAdd.symm]; exact GaloisField.card 2 _ (by omega))
    (f x') (f y') hfx hfy
  obtain ⟨h,hh⟩ := c.property
  refine ⟨h,?_⟩
  have hf : f ((simpleRoot Q split i).normalizerMonoidHom
      (inclusion (torus_normalizes_simpleRoot Q split i) h) x') = f y' := by
    rw [←suzukiBarAction_representative]
    exact (congrArg (fun k : MulAut (Multiplicative (BinaryGaloisField (2*m+1))) => k (f x')) hh).trans hc
  have he := square_eq_of_firstCoordinate_eq Q split i m μ hB _ _ hf
  rw [←map_pow] at he
  have he' := congrArg Subtype.val he
  change (h : X ⧸ Q.D)*x^2*(h : X ⧸ Q.D)⁻¹ = y^2 at he'
  rwa [hxa,hyb] at he'

include μ hB in
/-- Cartan conjugacy on the nonidentity elements of every shifted Omega root. -/
theorem suzuki_rootAt_omega_cartan_transitive (w : Weyl Q)
    (a b : X ⧸ Q.D) (ha : a ∈ omegaOneAmbient (rootAt Q split i w))
    (hb : b ∈ omegaOneAmbient (rootAt Q split i w)) (han : a ≠ 1) (hbn : b ≠ 1) :
    ∃ h : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)),
      (h : X ⧸ Q.D)*a*(h : X ⧸ Q.D)⁻¹ = b := by
  let n := representative w
  let e := MulAut.conj (n : X ⧸ Q.D)
  have he : (rootAt Q split i w).map e.toMonoidHom = simpleRoot Q split i := by
    change ((simpleRoot Q split i).comap e.toMonoidHom).map e.toMonoidHom = _
    exact map_comap_eq_self_of_surjective e.surjective _
  have hω : (omegaOneAmbient (rootAt Q split i w)).map e.toMonoidHom =
      omegaOneAmbient (simpleRoot Q split i) := by
    rw [map_omegaOneAmbient_injective e.toMonoidHom e.injective,he]
  obtain ⟨h,hh⟩ := suzuki_omega_cartan_transitive Q split i m μ hB (e a) (e b)
    (hω ▸ mem_map_of_mem e.toMonoidHom ha) (hω ▸ mem_map_of_mem e.toMonoidHom hb)
    (fun h => han (e.injective (h.trans (map_one e).symm)))
    (fun h => hbn (e.injective (h.trans (map_one e).symm)))
  let k := (Q.tits.B ⊓ Q.tits.N).normalizerMonoidHom
    ⟨(n : X ⧸ Q.D)⁻¹,torus_normalizes n⁻¹⟩ h
  refine ⟨k,?_⟩
  apply e.injective
  change (n : X ⧸ Q.D)*(((n : X ⧸ Q.D)⁻¹*h*((n : X ⧸ Q.D)⁻¹)⁻¹)*a*
    ((n : X ⧸ Q.D)⁻¹*h*((n : X ⧸ Q.D)⁻¹)⁻¹)⁻¹)*(n : X ⧸ Q.D)⁻¹ = e b
  calc
    _ = (h : X ⧸ Q.D)*e a*(h : X ⧸ Q.D)⁻¹ := by dsimp [e]; group
    _ = _ := hh

include μ hB in
/-- A Cartan-invariant subgroup containing one nonidentity Omega element contains the whole Omega. -/
theorem suzuki_rootAt_omega_le_of_invariant (w : Weyl Q) (D : Subgroup (X ⧸ Q.D))
    (hD : Q.tits.B ⊓ Q.tits.N ≤ normalizer (D : Set (X ⧸ Q.D)))
    (a : X ⧸ Q.D) (ha : a ∈ omegaOneAmbient (rootAt Q split i w))
    (haD : a ∈ D) (han : a ≠ 1) : omegaOneAmbient (rootAt Q split i w) ≤ D := by
  intro b hb
  by_cases hbn : b = 1
  · simpa only [hbn] using D.one_mem
  obtain ⟨h,hh⟩ := suzuki_rootAt_omega_cartan_transitive Q split i m μ hB w a b ha hb han hbn
  rw [←hh]
  exact (mem_normalizer_iff.mp (hD h.property) a).mp haD

include μ hB in
/-- The actual positive-parameter rank-one subgroup is generated by its Omega and reflection. -/
theorem positive_suzuki_omega_reflection_generate (hmpos : 0 < m)
    (s : RootReflection Q split i) :
    omegaOneAmbient (simpleRoot Q split i) ⊔ zpowers (s.val : X ⧸ Q.D) = rankOne Q split i := by
  let R := rankOne Q split i
  let f := suzukiActorEquiv Q split i m μ hB
  let Ω := omegaOneAmbient (simpleRoot Q split i)
  let r : R := ⟨s.val,s.mem_rankOne⟩
  have hΩ : Ω ≤ R := (omegaOneAmbient_le _).trans le_sup_left
  have hr : f r ∉ SuzukiBorelSubgroup m := by
    intro hh
    have hh' : f r ∈ (quotientBorel Q i).map μ.toMonoidHom := by
      rwa [hB,suzukiRootSubgroup_normalizer m hmpos]
    rw [mem_map_equiv] at hh'
    apply rootReflectionProjection_not_mem_borel Q split i s
    have he : inclusion (rankOne_le_parabolic Q split i) r = rootReflectionEndpoint Q split i s := Subtype.ext rfl
    simpa only [f,suzukiActorEquiv_apply,MulEquiv.symm_apply_apply,he] using hh'
  have hroot : ((simpleRoot Q split i).subgroupOf R).map f.toMonoidHom = SuzukiRootSubgroup m := by
    apply le_antisymm
    · rintro _ ⟨r,hr,rfl⟩
      exact (suzukiRootEquiv Q split i m μ hB ⟨r,hr⟩).property
    · intro x hx
      obtain ⟨a,ha⟩ := (suzukiRootEquiv Q split i m μ hB).surjective ⟨x,hx⟩
      exact ⟨inclusion le_sup_left a,a.property,congrArg Subtype.val ha⟩
  have hω : (Ω.subgroupOf R).map f.toMonoidHom = omegaOneAmbient (SuzukiRootSubgroup m) := by
    have ht := map_omegaOneAmbient_injective R.subtype R.subtype_injective
      ((simpleRoot Q split i).subgroupOf R)
    rw [map_subgroupOf_eq_of_le (show simpleRoot Q split i ≤ R from le_sup_left)] at ht
    have he : omegaOneAmbient ((simpleRoot Q split i).subgroupOf R) = Ω.subgroupOf R := by
      apply map_injective R.subtype_injective
      rw [ht,map_subgroupOf_eq_of_le hΩ]
    rw [←he,map_omegaOneAmbient_injective f.toMonoidHom f.injective,hroot]
  have hgen : Ω.subgroupOf R ⊔ zpowers r = ⊤ := by
    apply map_injective (f := f.toMonoidHom) f.injective
    rw [Subgroup.map_sup,hω,MonoidHom.map_zpowers,map_top_of_surjective f.toMonoidHom f.surjective]
    exact suzukiRootSubgroup_omega_sup_zpowers_eq_top m hmpos _ hr
  have he := congrArg (Subgroup.map R.subtype) hgen
  rwa [Subgroup.map_sup,map_subgroupOf_eq_of_le hΩ,MonoidHom.map_zpowers,←MonoidHom.range_eq_map,range_subtype] at he

include μ hB in
/-- Omega normalization of the perpendicular root extends to the whole positive Suzuki actor. -/
theorem positive_perpendicular_normalizes_of_omega_normalizes
    (hmpos : 0 < m) (hm : rotationOrder Q = 8) (j : Fin 2) (hij : i ≠ j)
    (hΩ : omegaOneAmbient (simpleRoot Q split i) ≤ normalizer
      (rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) : Set (X ⧸ Q.D))) :
    rankOne Q split i ≤ normalizer
      (rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) : Set (X ⧸ Q.D)) := by
  let s := UnitarySource.actorReflection Q split i
  rw [←positive_suzuki_omega_reflection_generate Q split i m μ hB hmpos s]
  exact sup_le hΩ (zpowers_le.mpr (perpendicular_root_normalizes Q split hm i j hij s.val s.class_eq))

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
