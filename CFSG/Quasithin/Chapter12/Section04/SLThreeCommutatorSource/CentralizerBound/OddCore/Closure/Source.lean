module
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound.OddCore.Endgame
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.ConjugateSpanCentralizer

/-!
# The abelian odd closure in the last branch of 12.4.8

Every element of M = N_G(V) either stabilizes the escaping hyperplane U or
moves it to a second hyperplane meeting U in a plane. The assumed plane-core
inclusions and their literal conjugates put both odd cores in that plane's
abelian odd core. Thus all generators of the M-conjugate closure commute.
In this abelian closure the seed lies in the intrinsic odd core; characteristicity
then puts the entire conjugate closure there, proving its odd order.

The plane-core premise is discharged by the ordinary-layer centralization
argument, owned with final 12.4.8 assembly by qt-d-1248-l3-centralizers. The
last theorem applies the closure result to the existing A.1.26 endgame.

Source: Aschbacher–Smith, 12.4.8, printed p.816.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound.OddCore
open Section02 SmallFusion ChapterE
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V U : Subgroup G}

/-- The literal intersection with every moving M-conjugate is a plane of U. -/
theorem moving_intersection (c : Configuration T L V U)
    {l : G} (hl : l ∈ normalizer (V : Set G))
    (hm : l ∉ normalizer (U : Set G)) :
    U ⊔ U.map (MulAut.conj l).toMonoidHom = V ∧
      Nat.card (U ⊓ U.map (MulAut.conj l).toMonoidHom : Subgroup G) = 4 ∧
      subgroupCorank U (U ⊓ U.map (MulAut.conj l).toMonoidHom) = 1 := by
  let _ := c.chosen.elementary
  let _ : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le c.le_module
  let W := U.map (MulAut.conj l).toMonoidHom
  let U₀ := U ⊓ W
  have hVfix := mem_normalizer_iff_map_conj_eq.mp hl
  have hWV : W ≤ V := (map_mono c.le_module).trans hVfix.le
  have hU := hyperplane_card c.extension c.fixed_nontrivial c.le_module c.corank
  have hV := module_card c.extension c.fixed_nontrivial
  have hW : Nat.card W = 8 := (card_map_of_injective (MulAut.conj l).injective).trans hU
  have hne : W ≠ U := fun he => hm (mem_normalizer_iff_map_conj_eq.mpr he)
  have hsup : U ⊔ W = V := by
    have hd : Nat.card (U ⊔ W : Subgroup G) ∣ 16 := hV ▸ card_dvd_of_le (sup_le c.le_module hWV)
    have hlo : 8 ≤ Nat.card (U ⊔ W : Subgroup G) := hU ▸ card_le_of_le le_sup_left
    have hneq : Nat.card (U ⊔ W : Subgroup G) ≠ 8 := by
      intro hc
      have he : U = U ⊔ W := eq_of_le_of_card_ge le_sup_left (by omega)
      exact hne (eq_of_le_of_card_ge (he ▸ (le_sup_right : W ≤ U ⊔ W)) (by omega))
    have he : Nat.card (U ⊔ W : Subgroup G) = 16 := by
      have hd' : Nat.card (U ⊔ W : Subgroup G) ∈ Nat.divisors 16 :=
        Nat.mem_divisors.mpr ⟨hd,by decide⟩
      have ht : Nat.divisors 16 = {1,2,4,8,16} := by decide
      rw [ht] at hd'
      simp only [Finset.mem_insert,Finset.mem_singleton] at hd'
      omega
    exact eq_of_le_of_card_ge (sup_le c.le_module hWV) (by omega)
  have hn : W ≤ normalizer (U : Set G) := by
    apply (show W ≤ centralizer (U : Set G) from ?_).trans (Subgroup.centralizer_le_normalizer _)
    intro w hw u hu
    exact setLike_mul_comm (c.le_module hu) (hWV hw)
  have hc : Nat.card U₀ = 4 := by
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes U W hn
    rw [hU,hW,hsup,hV] at hh
    change 8 * 8 = Nat.card U₀ * 16 at hh
    omega
  have hcor : subgroupCorank U U₀ = 1 := by
    have hi : U₀.relIndex U = 2 := by
      have hh := relIndex_mul_relIndex (⊥ : Subgroup G) U₀ U bot_le inf_le_left
      simp only [relIndex_bot_left] at hh
      rw [hc,hU] at hh
      omega
    rw [relIndex_eq_two_pow_quotient_finrank,← subgroupCorank_eq_quotient_finrank] at hi
    exact Nat.pow_right_injective (by decide : 2 ≤ 2) (by simpa using hi)
  exact ⟨hsup, hc, hcor⟩

omit [Finite G] in
private theorem centralizer_map_equiv (W : Subgroup G) (e : G ≃* G) :
    (centralizer (W : Set G)).map e.toMonoidHom =
      centralizer (W.map e.toMonoidHom : Set G) := by
  apply le_antisymm
  · exact map_centralizer_le_centralizer_image _ _
  · intro x hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    intro y hy
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using hx (e y) (mem_map_of_mem _ hy)

omit [Finite G] in
/-- Odd cores of centralizers commute with the specified ambient isomorphism. -/
theorem core_map_equiv (W : Subgroup G) (e : G ≃* G) :
    (core W).map e.toMonoidHom = core (W.map e.toMonoidHom) := by
  let C := centralizer (W : Set G)
  let D := centralizer (W.map e.toMonoidHom : Set G)
  let f : C ≃* D := (C.equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr (centralizer_map_equiv W e))
  calc
    (core W).map e.toMonoidHom = ((pPrimeCore 2 C).map f.toMonoidHom).map D.subtype := by
      simp only [core, map_map]
      rfl
    _ = core (W.map e.toMonoidHom) := by rw [pPrimeCore_map_iso]; rfl

omit [Finite G] in
private theorem map_conj_inv_conj (W : Subgroup G) (m : G) :
    (W.map (MulAut.conj m⁻¹).toMonoidHom).map (MulAut.conj m).toMonoidHom = W := by
  rw [map_map]
  have he : (MulAut.conj m).toMonoidHom.comp (MulAut.conj m⁻¹).toMonoidHom =
      MonoidHom.id G := by
    ext x
    simp [mul_assoc]
  rw [he, map_id]

/-- Plane containment forces the original odd core to commute with each M-conjugate. -/
theorem core_centralizes_conjugate (c : Configuration T L V U)
    (hplane : ∀ W ≤ U, subgroupCorank U W = 1 → core U ≤ core W)
    {m : G} (hm : m ∈ normalizer (V : Set G)) :
    core U ≤ centralizer ((core U).map (MulAut.conj m).toMonoidHom : Set G) := by
  obtain ⟨z, hz, hfix, hM, hi, hab, hplanes⟩ := simultaneous_inversion c
  by_cases hmU : m ∈ normalizer (U : Set G)
  · have he : (core U).map (MulAut.conj m).toMonoidHom = core U := by
      rw [core_map_equiv U (MulAut.conj m)]
      exact congrArg core (mem_normalizer_iff_map_conj_eq.mp hmU)
    rw [he]
    exact le_centralizer_iff_isMulCommutative.mpr hab
  · let W := U ⊓ U.map (MulAut.conj m).toMonoidHom
    have hg := moving_intersection c hm hmU
    have hmi : m⁻¹ ∉ normalizer (U : Set G) := by simpa using hmU
    have hgi := moving_intersection c ((normalizer (V : Set G)).inv_mem hm) hmi
    have hleft : core U ≤ core W := hplane W inf_le_left hg.2.2
    have he : (U ⊓ U.map (MulAut.conj m⁻¹).toMonoidHom).map
        (MulAut.conj m).toMonoidHom = W := by
      rw [map_inf _ _ _ (MulAut.conj m).injective, map_conj_inv_conj]
      exact inf_comm _ _
    have hright : (core U).map (MulAut.conj m).toMonoidHom ≤ core W := by
      have hh := map_mono (f := (MulAut.conj m).toMonoidHom)
        (hplane _ inf_le_left hgi.2.2)
      rwa [core_map_equiv (U ⊓ U.map (MulAut.conj m⁻¹).toMonoidHom) (MulAut.conj m), he] at hh
    have hc := le_centralizer_iff_isMulCommutative.mpr (hplanes W inf_le_left hg.2.2).2
    exact hleft.trans (hc.trans (centralizer_le hright))

/-- The actual M-conjugate closure is abelian. -/
theorem conjugateClosure_commutative (c : Configuration T L V U)
    (hplane : ∀ W ≤ U, subgroupCorank U W = 1 → core U ≤ core W) :
    IsMulCommutative (conjugateClosure V U) := by
  apply (conjugateSpanBy_commutative_iff _ _).mpr
  apply le_centralizer_iff.mpr
  apply (closure_le _).mpr
  rintro x ⟨m, hm, y, hy, rfl⟩
  exact (le_centralizer_iff.mp (core_centralizes_conjugate c hplane hm))
    (mem_map_of_mem (MulAut.conj m).toMonoidHom hy)

/-- In the abelian closure its odd seed, and therefore every conjugate, lies in O(P). -/
theorem conjugateClosure_odd_of_commutative
    (hc : IsMulCommutative (conjugateClosure V U)) :
    Nat.Coprime 2 (Nat.card (conjugateClosure V U)) := by
  let P := conjugateClosure V U
  let : IsMulCommutative P := hc
  let : CommGroup P := IsMulCommutative.instCommGroup
  have hle : core U ≤ P := le_conjugateSpanBy _ _
  let R := (core U).subgroupOf P
  have hR : R ≤ pPrimeCore 2 P := le_sSup ⟨inferInstance, by
    rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv]
    exact core_odd U⟩
  have hseed : core U ≤ (pPrimeCore 2 P).map P.subtype := by
    simpa only [R, map_subgroupOf_eq_of_le hle] using map_mono (f := P.subtype) hR
  have hP : P ≤ (pPrimeCore 2 P).map P.subtype :=
    conjugateSpanBy_le hseed ((le_normalizer_conjugateSpanBy _ _).trans
      (normalizer_le_normalizer_characteristic_image P (pPrimeCore 2 P)))
  have he : P = (pPrimeCore 2 P).map P.subtype := le_antisymm hP (map_subtype_le _)
  change Nat.Coprime 2 (Nat.card P)
  rw [he, card_map_of_injective P.subtype_injective]
  exact pPrimeCore_coprime_card

/-- The complete closure contract; only its declared plane-containment premise is used. -/
theorem closureConstruction : ClosureConstruction.{u} := by
  intro G _ _ T L V U c hplane
  have hc := conjugateClosure_commutative c hplane
  exact ⟨hc, conjugateClosure_odd_of_commutative hc⟩

omit [Finite G] in
/-- The closure contains its original nontrivial odd core. -/
theorem conjugateClosure_ne_bot (h : core U ≠ ⊥) : conjugateClosure V U ≠ ⊥ := by
  intro he
  apply h
  exact eq_bot_iff.mpr ((le_conjugateSpanBy (core U) (normalizer (V : Set G))).trans he.le)

omit [Finite G] in
/-- The original M normalizes the literal conjugate closure. -/
theorem normalizes_conjugateClosure (V U : Subgroup G) :
    normalizer (V : Set G) ≤ normalizer (conjugateClosure V U : Set G) :=
  le_normalizer_conjugateSpanBy _ _

/-- The actual odd-core case consumer, now retaining only ordinary-layer
centralization. Its remaining premise belongs to qt-d-1248-l3-centralizers. -/
theorem oddCoreExclusion_of_layer (layer : LayerCentralization.{u}) :
    OddCoreExclusion.{u} :=
  oddCoreExclusion_of_layer_and_closure layer closureConstruction

end CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound.OddCore
