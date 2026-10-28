module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.SourceOrbits.Representatives.FiveLocal.Placement
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.SourceOrbits.Representatives.FiveLocal.InternalPairs
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.FusionTypes
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.SpecificGroups.SymmetricFourSolvable

/-!
# Identifying and aligning the literal root of a five-local A₄ pair

Separation of the five-families puts the involutions of E(C_G(F)) in the
other involution class. In the marked E₄ × A₅ centralizer of an involution
of the pair's two-core, centralization by F forces this entire two-core
into E₄. Both groups have order four, so the literal pair root is a
conjugate of the 47.1 root.

Weak closure of the source cubic line in a Sylow three-subgroup makes
that line unique in every three-subgroup. In a marked A₄ × A₅ product,
this excludes a diagonal source cubic line: the pure first-factor line
in the same elementary nine-group already centralizes a conjugate of z.
The final calculation identifies the second factor with the intrinsic
component layer, using solvability of A₄ and quasisimplicity of A₅.

Source: Aschbacher, *Sporadic Groups* (1994), 47.1–47.3 and the second
paragraph of 47.5, printed pp.259–263. The earlier source conclusions
remain explicit inputs; no 47.5 pair or fixer assertion is assumed.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.Representatives.FiveLocal.RootMarking
open InvolutionGeometry
variable {G : Type*} [Group G] [Finite G] {D : Seed G}

omit [Finite G] in
private theorem centralizer_map (e : G ≃* G) (t : G) :
    (involutionCentralizer t).map e.toMonoidHom = involutionCentralizer (e t) := by
  apply le_antisymm
  · simpa only [Set.image_singleton, MulEquiv.coe_toMonoidHom] using
      map_centralizer_le_centralizer_image ({t} : Set G) e.toMonoidHom
  · intro x hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    apply mem_centralizer_singleton_iff.mpr
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using
      mem_centralizer_singleton_iff.mp hx

private noncomputable def centralizerEquiv (e : G ≃* G) (t : G) :
    involutionCentralizer t ≃* involutionCentralizer (e t) :=
  (e.subgroupMap _).trans (MulEquiv.subgroupCongr (centralizer_map e t))

private noncomputable def conjugateModel {t : G} (C : SecondCentralizer D t) (g : G) :
    SecondCentralizer D (MulAut.conj g t) where
  equiv := (centralizerEquiv (MulAut.conj g) t).symm.trans C.equiv
  fusion := by
    intro u hu
    let v := (centralizerEquiv (MulAut.conj g) t).symm u
    have hv : orderOf v = 2 :=
      ((centralizerEquiv (MulAut.conj g) t).symm.orderOf_eq u).trans hu
    have hconj : IsConj (v : G) (u : G) := isConj_iff.mpr ⟨g, by
      change (MulAut.conj g) ((MulAut.conj g).symm (u : G)) = (u : G)
      exact MulEquiv.apply_symm_apply _ _⟩
    exact (show IsConj D.z (u : G) ↔ IsConj D.z (v : G) from
      ⟨fun h => h.trans hconj.symm, fun h => h.trans hconj⟩).trans (C.fusion v hv)

private noncomputable def coreEquiv (Y : D.Vertex)
    (eJ : pairJoin D Y ≃* A4) : pairRoot D Y ≃* alternatingGroup.kleinFour (Fin 4) :=
  ((pCore 2 (pairJoin D Y)).equivMapOfInjective (pairJoin D Y).subtype
    (pairJoin D Y).subtype_injective).symm.trans
    (((pCore 2 (pairJoin D Y)).equivMapOfInjective eJ.toMonoidHom eJ.injective).trans
      (MulEquiv.subgroupCongr ((pCore_map_iso 2 eJ).trans AlternatingFourPair.twoCore_eq_kleinFour)))

private theorem core_card (Y : D.Vertex) (eJ : pairJoin D Y ≃* A4) : Nat.card (pairRoot D Y) = 4 := by
  rw [Nat.card_congr (coreEquiv Y eJ).toEquiv]
  exact alternatingGroup.kleinFour_card_of_card_eq_four (by norm_num)

private theorem core_square (Y : D.Vertex) (eJ : pairJoin D Y ≃* A4)
    (u : pairRoot D Y) : u ^ 2 = 1 := by
  apply (coreEquiv Y eJ).injective
  rw [map_pow, map_one]
  have he := alternatingGroup.exponent_kleinFour_of_card_eq_four
    (α := Fin 4) (by norm_num)
  simpa only [he] using Monoid.pow_exponent_eq_one ((coreEquiv Y eJ) u)

private theorem core_commute (Y : D.Vertex) (eJ : pairJoin D Y ≃* A4)
    (u v : pairRoot D Y) : Commute u v := by
  have h := core_square Y eJ (u * v)
  have hu := core_square Y eJ u
  have hv := core_square Y eJ v
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hu)
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hv)
  have hi : (u * v)⁻¹ = u * v := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using h)
  change u * v = v * u
  simpa only [mul_inv_rev, hui, hvi] using hi.symm

/-- Separation of the two five-families puts every involution of this component
in the other involution class. -/
theorem component_involution_other (S : SelectedGeometry D)
    (P : EarlierFive.PlacedComponent D S.t)
    (hsep : PrimeNormalizers.FiveLocal.TwoCentralFiveFamily D S.t)
    {u : G} (hu : u ∈ PrimeNormalizers.FiveLocal.fiveComponent P.F)
    (ho : orderOf u = 2) : OtherInvolution D u := by
  refine ⟨ho, fun hc => hsep.separated P.F P.five ?_⟩
  refine ⟨P.five.1, u, hc, ?_⟩
  have huc : u ∈ centralizer (P.F : Set G) := (map_subtype_le _) hu
  intro f hf
  exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp huc f hf)

private theorem five_centralizing_square (a b : A5)
    (ha : a ^ 2 = 1) (hb : b ^ 5 = 1) (hne : b ≠ 1)
    (hc : a * b = b * a) : a = 1 := by
  have h : ∀ a b : A5, a ^ 2 = 1 → b ^ 5 = 1 → b ≠ 1 → a * b = b * a → a = 1 := by
    decide +kernel
  exact h a b ha hb hne hc

/-- In the marked second centralizer, an involution centralized by a five-element
lies in the literal two-core. -/
private theorem square_mem_rootCore {t : G} (C : SecondCentralizer D t)
    (u f : involutionCentralizer t) (hu : u ^ 2 = 1)
    (hf : orderOf f = 5) (hc : Commute u f) : (u : G) ∈ rootCore t := by
  apply (C.mem_rootCore_iff u).mpr
  have hfsq : (C.equiv f).1 ^ 2 = 1 := by
    have h : ∀ a : E4, a ^ 2 = 1 := by decide +kernel
    exact h _
  have hffifth : (C.equiv f).1 ^ 5 = 1 := by
    have h := congrArg (fun v => (C.equiv v).1) (pow_orderOf_eq_one f)
    simpa only [hf, map_pow, map_one, Prod.pow_fst, Prod.fst_one] using h
  have hf1 : (C.equiv f).1 = 1 := by
    have h2 := orderOf_dvd_of_pow_eq_one hfsq
    have h5 := orderOf_dvd_of_pow_eq_one hffifth
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp (show orderOf (C.equiv f).1 ∣ 1 from Nat.dvd_gcd h2 h5))
  have hf2 : (C.equiv f).2 ≠ 1 := by
    intro h
    have he : f = 1 := C.equiv.injective ((Prod.ext hf1 h).trans C.equiv.map_one.symm)
    rw [he, orderOf_one] at hf
    omega
  apply five_centralizing_square _ _
  · simpa only [map_pow, map_one, Prod.pow_snd, Prod.snd_one] using
      congrArg (fun v => (C.equiv v).2) hu
  · simpa only [hf, map_pow, map_one, Prod.pow_snd, Prod.snd_one] using
      congrArg (fun v => (C.equiv v).2) (pow_orderOf_eq_one f)
  · exact hf2
  · simpa only [map_mul, Prod.snd_mul] using congrArg (fun v => (C.equiv v).2) hc.eq

/-- The A₄ pair's literal two-core is an actual conjugate of the 47.1 root. -/
theorem core_is_conjugate (S : SelectedGeometry D)
    (P : EarlierFive.PlacedComponent D S.t)
    (hsep : PrimeNormalizers.FiveLocal.TwoCentralFiveFamily D S.t)
    (Y : D.Vertex) (hY : Y.val ≤ PrimeNormalizers.FiveLocal.fiveComponent P.F)
    (eJ : pairJoin D Y ≃* A4) :
    ∃ g : G, (rootCore S.t).map (MulAut.conj g).toMonoidHom = pairRoot D Y := by
  have hUL : pairRoot D Y ≤ PrimeNormalizers.FiveLocal.fiveComponent P.F :=
    (pCoreIn_le _ _).trans (sup_le P.X_le hY)
  have hUne : pairRoot D Y ≠ ⊥ := by
    intro he
    have hh := core_card Y eJ
    rw [he, card_bot] at hh
    omega
  obtain ⟨u, hu, hune⟩ := (pairRoot D Y).bot_or_exists_ne_one.resolve_left hUne
  have huo : orderOf u = 2 := orderOf_eq_prime
    (congrArg Subtype.val (core_square Y eJ ⟨u, hu⟩)) hune
  have huo' := component_involution_other S P hsep (hUL hu) huo
  obtain ⟨g, hg⟩ := isConj_iff.mp (S.other.isConj huo')
  let C : SecondCentralizer D u := hg ▸ conjugateModel S.model g
  have hUu : pairRoot D Y ≤ involutionCentralizer u := by
    intro v hv
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (core_commute Y eJ ⟨v,hv⟩ ⟨u,hu⟩).eq)
  have hFu : P.F ≤ involutionCentralizer u := by
    intro f hf
    exact mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp ((map_subtype_le _) (hUL hu)) f hf)
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨f, hf⟩ := exists_prime_orderOf_dvd_card' (G := P.F) 5 (by rw [P.five.1])
  have hUr : pairRoot D Y ≤ rootCore u := by
    intro v hv
    apply square_mem_rootCore C ⟨v, hUu hv⟩ ⟨f, hFu f.property⟩
    · exact Subtype.ext (show v ^ 2 = 1 from congrArg (fun x : pairRoot D Y => (x : G)) (core_square Y eJ ⟨v,hv⟩))
    · simpa only [← Subgroup.orderOf_coe] using hf
    · apply Subtype.ext
      exact (mem_centralizer_iff.mp ((map_subtype_le _) (hUL hv)) f f.property).symm
  have he : pairRoot D Y = rootCore u := eq_of_le_of_card_ge hUr
    (by rw [C.rootCore_card, core_card Y eJ])
  refine ⟨g, (rootCore_map S.t (MulAut.conj g)).trans ?_⟩
  change rootCore (g * S.t * g⁻¹) = pairRoot D Y
  rw [hg, ← he]

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.Representatives.FiveLocal.RootMarking

open scoped Pointwise
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.Representatives.FiveLocal.RootMarking
open InvolutionGeometry PrimeNormalizers.ThreeLocal
variable {G : Type*} [Group G] [Finite G] {D : Seed G}

/-- Weak closure in 47.3 makes the source vertex inside any three-subgroup unique. -/
theorem vertex_unique_in_three_subgroup
    (hSyl : ∀ Q : Sylow 3 G, Nonempty (SylowThreeStructure D Q))
    (H : Subgroup G) (hH : IsPGroup 3 H) (V W : D.Vertex)
    (hV : V.val ≤ H) (hW : W.val ≤ H) : V.val = W.val := by
  obtain ⟨Q, hQ⟩ := hH.exists_le_sylow
  obtain ⟨T⟩ := hSyl Q
  have hv (A : D.Vertex) (hA : A.val ≤ H) :
      A.val = (center Q).map (Q : Subgroup G).subtype := by
    have horb : A.val ∈ MulAction.orbit (ConjAct G)
        ((center Q).map (Q : Subgroup G).subtype) := by
      rw [MulAction.orbit_eq_iff.mpr T.center_vertex]
      exact A.property
    obtain ⟨g, hg⟩ := horb
    change ((center Q).map (Q : Subgroup G).subtype).map
      (MulAut.conj (ConjAct.ofConjAct g)).toMonoidHom = A.val at hg
    exact hg.symm.trans (T.weakly_closed _ (hg.symm ▸ hA.trans hQ))
  exact (hv V hV).trans (hv W hW).symm

private theorem cubic_in_line (a : A4) (ha : a ^ 3 = 1) :
    ∃ c : A4, orderOf c = 3 ∧ a ∈ zpowers c := by
  by_cases h : a = 1
  · let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := A4) 3 (by
      rw [nat_card_alternatingGroup]; norm_num)
    exact ⟨c, hc, h ▸ one_mem _⟩
  · exact ⟨a, orderOf_eq_prime ha h, mem_zpowers a⟩

/-- The cubic-line uniqueness excludes diagonal source vertices in the marked
A₄ × A₅ normalizer. The second factor meets the distinguished involution class. -/
theorem vertex_le_firstFactor
    (hSyl : ∀ Q : Sylow 3 G, Nonempty (SylowThreeStructure D Q))
    (f : A4 × A5 →* G) (hf : Function.Injective f)
    (hz : ∃ z : A5, IsConj D.z (f (1,z)))
    (V : D.Vertex) (hV : V.val ≤ f.range) :
    V.val ≤ ((⊤ : Subgroup A4).prod (⊥ : Subgroup A5)).map f := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' (G := V.val) 3
    (by rw [D.vertex_card V])
  have hvg : zpowers (v : G) = V.val := eq_of_le_of_card_ge
    (zpowers_le.mpr v.property) (by rw [Nat.card_zpowers, orderOf_coe, hv, D.vertex_card V])
  obtain ⟨a, ha⟩ := hV v.property
  have ha3 : a ^ 3 = 1 := hf (by
    rw [map_pow, ha, map_one]
    exact congrArg Subtype.val (hv ▸ pow_orderOf_eq_one v))
  obtain ⟨c, hc, hac⟩ := cubic_in_line a.1 (congrArg Prod.fst ha3)
  let u := f (c,1)
  have hu : orderOf u = 3 := by
    rw [orderOf_injective f hf]
    simpa only [Prod.orderOf, orderOf_one, Nat.lcm_one_right] using hc
  obtain ⟨z, hz⟩ := hz
  have huz : Commute u (f (1,z)) := by
    apply Commute.map
    exact (show Commute ((c,1) : A4 × A5) (1,z) from Prod.ext (by simp) (by simp))
  have hU : zpowers u ∈ MulAction.orbit (ConjAct G) D.X :=
    ((threeA_iff_centralizes D u).mpr ⟨hu, f (1,z), hz, huz⟩).2
  let B := (zpowers c).prod (zpowers a.2)
  have hB : IsPGroup 3 B := by
    intro x
    refine ⟨1, ?_⟩
    change x ^ 3 = 1
    apply Subtype.ext
    apply Prod.ext
    · exact orderOf_dvd_iff_pow_eq_one.mp
        ((orderOf_dvd_of_mem_zpowers x.property.1).trans (by rw [hc]))
    · exact orderOf_dvd_iff_pow_eq_one.mp
        ((orderOf_dvd_of_mem_zpowers x.property.2).trans
          (orderOf_dvd_of_pow_eq_one (congrArg Prod.snd ha3)))
  have hUB : zpowers u ≤ B.map f := zpowers_le.mpr
    (mem_map.mpr ⟨(c,1), ⟨mem_zpowers c, one_mem _⟩, rfl⟩)
  have hVB : V.val ≤ B.map f := by
    rw [← hvg]
    exact zpowers_le.mpr (mem_map.mpr ⟨a, ⟨hac, mem_zpowers _⟩, ha⟩)
  have he := vertex_unique_in_three_subgroup hSyl (B.map f) (hB.map f)
    ⟨zpowers u,hU⟩ V hUB hVB
  rw [← he]
  exact zpowers_le.mpr (mem_map.mpr ⟨(c,1), ⟨mem_top _, rfl⟩, rfl⟩)

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.Representatives.FiveLocal.RootMarking

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.Representatives.FiveLocal.RootMarking
open InvolutionGeometry

private theorem map_layer_le {H K : Type*} [Group H] [Group K] (e : H ≃* K) :
    (componentLayer H).map e.toMonoidHom ≤ componentLayer K := by
  apply map_le_iff_le_comap.mpr
  apply sSup_le
  intro J hJ
  exact map_le_iff_le_comap.mp (le_sSup (hJ.map_equiv e))

private theorem map_layer {H K : Type*} [Group H] [Group K] (e : H ≃* K) :
    (componentLayer H).map e.toMonoidHom = componentLayer K := by
  apply le_antisymm (map_layer_le e)
  have hm := map_mono (f := e.toMonoidHom) (map_layer_le e.symm)
  simpa [map_map] using hm

private theorem layer_product :
    componentLayer (A4 × A5) = (⊥ : Subgroup A4).prod (⊤ : Subgroup A5) := by
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let : Group.IsSolvable A4 := inferInstance
  let : IsQuasisimple A5 := {
    toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    simple := by
      let : IsSimpleGroup A5 := alternatingGroup.isSimpleGroup (by simp)
      exact ((QuotientGroup.quotientMulEquivOfEq
        (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup }
  let B := (⊥ : Subgroup A4).prod (⊤ : Subgroup A5)
  let eB : B ≃* A5 := (Subgroup.prodEquiv _ _).trans
    (MulEquiv.uniqueProd.trans Subgroup.topEquiv)
  apply le_antisymm
  · apply sSup_le
    intro K hK
    let := hK.2
    have hf : K.map (MonoidHom.fst A4 A5) = ⊥ := by
      let : Group.IsPerfect (K.map (MonoidHom.fst A4 A5)) := Group.IsPerfect.map _
      by_contra hn
      let : Nontrivial (K.map (MonoidHom.fst A4 A5)) := (nontrivial_iff_ne_bot _).mpr hn
      exact Group.IsPerfect.not_isSolvable (K.map (MonoidHom.fst A4 A5)) inferInstance
    intro a ha
    exact ⟨mem_bot.mp (hf ▸ mem_map_of_mem (MonoidHom.fst A4 A5) ha), mem_top _⟩
  · apply le_sSup
    exact ⟨(inferInstance : B.Normal).isSubnormal, IsQuasisimple.of_mulEquiv eB.symm⟩

/-- The actual intrinsic layer in arbitrary coordinates of this product. -/
theorem layer_in_coordinates {H : Type*} [Group H] (e : H ≃* (A4 × A5)) :
    ((⊥ : Subgroup A4).prod (⊤ : Subgroup A5)).map e.symm.toMonoidHom =
      componentLayer H := by
  rw [← layer_product]
  exact map_layer e.symm

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.Representatives.FiveLocal.RootMarking
