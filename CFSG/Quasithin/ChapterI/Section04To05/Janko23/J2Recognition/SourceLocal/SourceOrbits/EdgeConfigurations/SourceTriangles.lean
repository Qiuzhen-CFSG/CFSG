module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.SourceOrbits.EdgeConfigurations.LocalIncidence
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.SourceOrbits.EdgeConfigurations.QuotientDoubleCosets
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Applications

/-!
# The two source triangle orbits

The fifteen inner vertices form one orbit of the pointwise A₅ edge fixer.
A Sylow four-group fixes a vertex in this odd set; the full centralizer of
that pure four-group gives an SL₂(3) join. The source pair stabilizer is a
two-group, forcing an orbit of size fifteen. Thus the inner calculation
needs no identification of the fixer intersection with A₄.

For the outer branch, the local A₅ has full centralizer equal to the
marked D₁₀. Its external triangle therefore has a fixer orbit of size six.
Local cubic incidence makes the three X-translates disjoint, so their
eighteen vertices exhaust the outer range. This proves external common-
neighbor transitivity from the seed alone, with no double-coset or orbit
premise. Exhaustion also places every outer triple in an actual A₅,
proves the one-plus-two incidence partition, and gives the fifteen and
twelve intersection counts. Thus adjacent vertices have eight common
neighbors (correcting the printed 18 in 47.6(3)). The separate internal
branch uses the setwise edge stabilizer.

Source: Aschbacher, *Sporadic Groups* (1994), 47.6(1),(2),(5), p.264,
and the local construction in 47.10, pp.266–267. The pure four-group
centralizer and source suborbits are the already proved 46.3, 46.14 and
47.1–47.5 inputs. The argument preserves the literal subgroup embeddings
and left conjugation throughout.
-/

public section
open Subgroup MulAction
open Theory.GroupTheory.GraphUniquenessSystem
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.EdgeConfigurations
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]

private theorem source_fixer_involutions (D : Seed G) (Y : D.Vertex)
    (hY : D.graph.Adj D.base Y) {u : G}
    (hu : u ∈ fixer D Y) (ho : orderOf u = 2) : IsConj D.z u := by
  obtain ⟨S, hfive, hthree⟩ := InvolutionGeometry.Applications.source_prime_local D
  exact Representatives.edge_involutions_conjugate_of_earlier_source
    S hfive.root hfive.twoCentral hthree.sylow hthree.normalizer_card
    hthree.local_normalizer_card (InvolutionGeometry.card_eq D) hY hu ho

omit [IsSimpleGroup G] in
private theorem source_five (D : Seed G) : PrimeNormalizers.FiveNormalizerTypes G := by
  obtain ⟨S⟩ := InvolutionGeometry.selectedGeometry_of_seed D
  exact PrimeNormalizers.FiveLocal.fiveNormalizerTypes_of_selectedGeometry
    (InvolutionGeometry.card_eq D) S

private theorem source_calculation (D : Seed G) :
    Nonempty (PrimeNormalizers.ThreeLocal.CentralizerCalculation D) := by
  obtain ⟨S⟩ := InvolutionGeometry.selectedGeometry_of_seed D
  exact PrimeNormalizers.centralizerCalculation_of_selectedGeometry
    (InvolutionGeometry.card_eq D) S

/-- An embedded pure four-group suffices for the inner source incidence.
No identification of the entire intersection with A₄ is needed. -/
theorem inner_sl2Join_of_four_subgroup (D : Seed G) (Y : D.Vertex)
    (hY : D.graph.Adj D.base Y) (g : localCentralizer D)
    (hg : (g : G) ∉ actor D Y) (E : Subgroup G)
    (hE : E ≤ intersection D Y g) (hfour : IsKleinFour E) :
    sl2Join D Y ((g : G) • Y) := by
  let := hfour
  have hF := InvolutionGeometry.Applications.edgeFixer_equiv D hY
  have hpure : ∀ t ∈ E, t ≠ 1 → IsConj D.z t := by
    intro t ht hne
    have hs : (⟨t, ht⟩ : E) ^ 2 = 1 := by
      simpa only [pow_two] using IsKleinFour.mul_self (⟨t, ht⟩ : E)
    exact source_fixer_involutions D Y hY (hE ht).1
      (orderOf_eq_prime (by simpa using congrArg Subtype.val hs) hne)
  obtain ⟨e⟩ := PureFourCentralizer.models D E hfour hpure
  let gn : localNormalizer D := ⟨g, Subgroup.centralizer_le_normalizer _ g.property⟩
  have ht := triple_le_centralizer D Y hF gn E hE
  have hadj : D.graph.Adj D.base ((g : G) • Y) := by
    have h := D.preserves (g : G) hY
    rwa [normalizer_fixes_base D gn] at h
  exact sl2Join_of_root_model rootModelCubicGeometry D _ e Y ((g : G) • Y)
    (le_sup_left.trans (le_sup_left.trans ht))
    (le_sup_right.trans (le_sup_left.trans ht)) (le_sup_right.trans ht) hY hadj
    (inner_not_endpointOrbit D Y _ ⟨g, g.property, hg, rfl⟩)

omit [IsSimpleGroup G] in
private theorem outer_smul_mem (D : Seed G) (Y : D.Vertex)
    (a : localCentralizer D) {U : D.Vertex} (hU : U ∈ outerSet D Y) :
    (a : G) • U ∈ outerSet D Y := by
  obtain ⟨g, hg, hgl, rfl⟩ := hU
  refine ⟨(a : G) * g, (localNormalizer D).mul_mem
    (Subgroup.centralizer_le_normalizer _ a.property) hg, ?_, mul_smul _ _ _⟩
  intro h
  apply hgl
  simpa only [inv_mul_cancel_left] using
    (localCentralizer D).mul_mem ((localCentralizer D).inv_mem a.property) h

private theorem X_smul_injective (D : Seed G) (U : D.Vertex)
    (hU : D.graph.Adj D.base U) :
    Function.Injective (fun x : D.X => (x : G) • U) := by
  intro x y h
  change (x : G) • U = (y : G) • U at h
  have hfix : (y : G)⁻¹ * x ∈ fixer D U := by
    refine ⟨normalizer_fixes_base D ⟨(y : G)⁻¹ * x,
      D.X.le_normalizer (D.X.mul_mem (D.X.inv_mem y.property) x.property)⟩, ?_⟩
    change ((y : G)⁻¹ * x) • U = U
    rw [mul_smul, h, inv_smul_smul]
  have he : (y : G)⁻¹ * x = 1 :=
    (disjoint_iff.mp (fixer_disjoint_X D U
      (InvolutionGeometry.Applications.edgeFixer_equiv D hU))).le
      ⟨hfix, D.X.mul_mem (D.X.inv_mem y.property) x.property⟩
  exact Subtype.ext (inv_mul_eq_one.mp he).symm

private theorem outer_decomposition_of_single_orbit (D : Seed G) (Y : D.Vertex)
    (hY : D.graph.Adj D.base Y)
    (U V : D.Vertex) (hU : U ∈ outerSet D Y) (hV : V ∈ outerSet D Y)
    (hUY : D.graph.Adj Y U)
    (hc : Nat.card (orbit (fixer D Y) U) = 6)
    (huq : ∃! W : D.Vertex, W ∈ orbit D.X U ∧ D.graph.Adj Y W) :
    ∃ x : D.X, ∃ f : fixer D Y, (x : G) • ((f : G) • U) = V := by
  classical
  have hF := InvolutionGeometry.Applications.edgeFixer_equiv D hY
  have hbase (W : D.Vertex) (hW : W ∈ outerSet D Y) : D.graph.Adj D.base W := by
    obtain ⟨g, hg, _, rfl⟩ := hW
    have h := D.preserves g hY
    rwa [normalizer_fixes_base D ⟨g, hg⟩] at h
  have horb (W : orbit (fixer D Y) U) :
      (W : D.Vertex) ∈ outerSet D Y ∧ D.graph.Adj Y W := by
    obtain ⟨f, hf⟩ := W.property
    change (f : G) • U = (W : D.Vertex) at hf
    constructor
    · rw [← hf]
      exact outer_smul_mem D Y ⟨f, fixer_le_localCentralizer D Y hF f.property⟩ hU
    · have h := D.preserves (f : G) hUY
      rwa [show (f : G) • Y = Y from f.property.2, hf] at h
  have unique (W : orbit (fixer D Y) U) (x : D.X)
      (hx : D.graph.Adj Y ((x : G) • (W : D.Vertex))) :
      (x : G) • (W : D.Vertex) = W := by
    obtain ⟨f, hf⟩ := W.property
    change (f : G) • U = (W : D.Vertex) at hf
    have he : (x : G) • (W : D.Vertex) = (f : G) • ((x : G) • U) := by
      rw [← hf, ← mul_smul, ← mul_smul,
        fixer_le_localCentralizer D Y hF f.property x x.property]
    have hxU : D.graph.Adj Y ((x : G) • U) := by
      have h := D.preserves (f : G)⁻¹ hx
      rwa [he, inv_smul_smul,
        show (f : G)⁻¹ • Y = Y from (fixer D Y).inv_mem f.property |>.2] at h
    have hu : (x : G) • U = U := huq.unique
      ⟨⟨x, rfl⟩, hxU⟩ ⟨mem_orbit_self _, hUY⟩
    rw [he, hu, hf]
  let p : D.X × orbit (fixer D Y) U → outerSet D Y := fun q =>
    ⟨(q.1 : G) • (q.2 : D.Vertex), outer_smul_mem D Y
      ⟨q.1, PrimeNormalizers.ThreeLocal.X_le_C D q.1.property⟩ (horb q.2).1⟩
  have hinj : Function.Injective p := by
    rintro ⟨x, W⟩ ⟨y, Z⟩ he
    have he' : (x : G) • (W : D.Vertex) = (y : G) • (Z : D.Vertex) :=
      congrArg Subtype.val he
    have hdiff : ((y : G)⁻¹ * x) • (W : D.Vertex) = Z := by
      rw [mul_smul, he', inv_smul_smul]
    have hwz : (W : D.Vertex) = Z :=
      (unique W (y⁻¹ * x) (by simpa only [Subgroup.coe_mul, Subgroup.coe_inv, hdiff]
        using (horb Z).2)).symm.trans hdiff
    have hxy : x = y := X_smul_injective D W (hbase W (horb W).1) (by rwa [← hwz] at he')
    exact Prod.ext hxy (Subtype.ext hwz)
  have hcard : Nat.card (D.X × orbit (fixer D Y) U) = Nat.card (outerSet D Y) := by
    obtain ⟨H⟩ := source_calculation D
    rw [Nat.card_prod, D.card_X, hc, outerSet_card D H Y hF]
  have hsurj := ((Nat.bijective_iff_injective_and_card p).mpr ⟨hinj, hcard⟩).2
  obtain ⟨⟨x, W⟩, hx⟩ := hsurj ⟨V, hV⟩
  have hx' : (x : G) • (W : D.Vertex) = V := congrArg Subtype.val hx
  obtain ⟨f, hf⟩ := W.property
  change (f : G) • U = (W : D.Vertex) at hf
  exact ⟨x, f, by rw [hf]; exact hx'⟩

private theorem outer_transporter_of_single_orbit (D : Seed G) (Y : D.Vertex)
    (hY : D.graph.Adj D.base Y)
    (U V : D.Vertex) (hU : U ∈ outerSet D Y) (hV : V ∈ outerSet D Y)
    (hUY : D.graph.Adj Y U) (hVY : D.graph.Adj Y V)
    (hc : Nat.card (orbit (fixer D Y) U) = 6)
    (huq : ∃! W : D.Vertex, W ∈ orbit D.X U ∧ D.graph.Adj Y W) :
    ∃ f : fixer D Y, (f : G) • U = V := by
  obtain ⟨x, f, hf⟩ := outer_decomposition_of_single_orbit D Y hY U V hU hV hUY hc huq
  have hF := InvolutionGeometry.Applications.edgeFixer_equiv D hY
  have he : (x : G) • ((f : G) • U) = (f : G) • ((x : G) • U) := by
    rw [← mul_smul, ← mul_smul,
      fixer_le_localCentralizer D Y hF f.property x x.property]
  have hadj : D.graph.Adj Y ((x : G) • U) := by
    have h := D.preserves (f : G)⁻¹ hVY
    rw [← hf, he, inv_smul_smul,
      show (f : G)⁻¹ • Y = Y from (fixer D Y).inv_mem f.property |>.2] at h
    exact h
  have hu : (x : G) • U = U := huq.unique
    ⟨⟨x, rfl⟩, hadj⟩ ⟨mem_orbit_self _, hUY⟩
  exact ⟨f, by rwa [he, hu] at hf⟩

private theorem sl2_fixer_isPGroup (D : Seed G) (A B : D.Vertex)
    (h : sl2Join D A B) : IsPGroup 2 (edgeFixer G A B) := by
  obtain ⟨g, rfl⟩ := D.transitive A
  have hbase : sl2Join D D.base (g⁻¹ • B) := by
    apply (sl2Join_smul_iff D g D.base (g⁻¹ • B)).mp
    simpa only [smul_inv_smul] using h
  obtain ⟨S⟩ := InvolutionGeometry.selectedGeometry_of_seed D
  obtain ⟨R⟩ := PrimeNormalizers.threePairRepresentatives_of_selectedGeometry
    (InvolutionGeometry.card_eq D) S
  have hm := (PrimeNormalizers.source_prime_local_of_selectedGeometry
    (InvolutionGeometry.card_eq D) S).2.normalizer_card
  obtain ⟨P, hP⟩ := R.sl_stabilizer_sylow (InvolutionGeometry.card_eq D) hm hbase
  have hp : IsPGroup 2 (edgeFixer G D.base (g⁻¹ • B)) :=
    (hP ▸ P.isPGroup').of_equiv (normalizerStabilizerEquiv D (g⁻¹ • B))
  have he : (edgeFixer G D.base (g⁻¹ • B)).map (MulAut.conj g).toMonoidHom =
      edgeFixer G (g • D.base) B := by
    rw [edgeFixer, map_inf _ _ _ (MulAut.conj g).injective,
      ← stabilizer_smul_eq_stabilizer_map_conj,
      ← stabilizer_smul_eq_stabilizer_map_conj, smul_inv_smul]
    rfl
  exact he ▸ hp.map (MulAut.conj g).toMonoidHom

omit [IsSimpleGroup G] in
private theorem inner_fixer_smul_mem (D : Seed G) (Y : D.Vertex)
    (hF : Nonempty (fixer D Y ≃* alternatingGroup (Fin 5)))
    (f : fixer D Y) {U : D.Vertex} (hU : U ∈ innerSet D Y) :
    (f : G) • U ∈ innerSet D Y := by
  obtain ⟨g, hg, hga, rfl⟩ := hU
  refine ⟨(f : G) * g, (localCentralizer D).mul_mem
    (fixer_le_localCentralizer D Y hF f.property) hg, ?_, mul_smul _ _ _⟩
  intro ha
  apply hga
  simpa only [inv_mul_cancel_left] using (actor D Y).mul_mem
    ((actor D Y).inv_mem ((le_sup_left : fixer D Y ≤ actor D Y) f.property)) ha

omit [IsSimpleGroup G] in
private theorem sylow_fixer_four (D : Seed G) (Y : D.Vertex)
    (hF : Nonempty (fixer D Y ≃* alternatingGroup (Fin 5))) (P : Sylow 2 (fixer D Y)) :
    IsKleinFour P := by
  have hc : Nat.card (fixer D Y) = 60 := by
    rw [Nat.card_congr hF.some.toEquiv, nat_card_alternatingGroup]
    norm_num
  have hp : Nat.card P = 4 := by
    rw [P.card_eq_multiplicity, hc]
    decide +kernel
  have : Nontrivial P := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  refine ⟨hp, (Monoid.exponent_eq_prime_iff Nat.prime_two).mpr ?_⟩
  intro p hne
  have hcub : ∀ a : alternatingGroup (Fin 5), a ^ 4 = 1 → a ^ 2 = 1 := by
    decide +kernel
  apply orderOf_eq_prime _ hne
  apply Subtype.ext
  apply hF.some.injective
  change hF.some ((p : fixer D Y) ^ 2) = hF.some 1
  rw [map_pow, map_one]
  apply hcub
  rw [← map_pow, ← hp]
  simpa only [Subgroup.coe_pow, Subgroup.coe_one, map_one] using congrArg (fun q : P => hF.some q.val) (pow_card_eq_one' (x := p))

/-- The fifteen inner vertices form one orbit of the pointwise edge fixer,
and every one generates SL₂(3) with Y. A Sylow four-group has a fixed point
on the odd inner set; its pure four-group centralizer supplies the join.
The pair stabilizer is a two-group, forcing this orbit to have all fifteen points. -/
theorem inner_source_orbit (D : Seed G) (Y : D.Vertex)
    (hY : D.graph.Adj D.base Y) :
    (∀ U ∈ innerSet D Y, sl2Join D Y U) ∧
    (∀ U ∈ innerSet D Y, ∀ V ∈ innerSet D Y,
      ∃ f : fixer D Y, (f : G) • U = V) := by
  classical
  have hF := InvolutionGeometry.Applications.edgeFixer_equiv D hY
  obtain ⟨H⟩ := source_calculation D
  have hcard := innerSet_card D H Y hF
  let P : Sylow 2 (fixer D Y) := Classical.choice inferInstance
  let A : SubMulAction (fixer D Y) D.Vertex := {
    carrier := innerSet D Y
    smul_mem' := inner_fixer_smul_mem D Y hF }
  obtain ⟨U, hU⟩ := P.isPGroup'.nonempty_fixed_point_of_prime_not_dvd_card A
    (by change ¬ 2 ∣ Nat.card (innerSet D Y); rw [hcard]; decide)
  let E : Subgroup G := (P : Subgroup (fixer D Y)).map (fixer D Y).subtype
  have hEP : E ≃* P :=
    ((P : Subgroup (fixer D Y)).equivMapOfInjective (fixer D Y).subtype
      (fixer D Y).subtype_injective).symm
  have hfP := sylow_fixer_four D Y hF P
  have hfE : IsKleinFour E := ⟨(Nat.card_congr hEP.toEquiv).trans hfP.card_four,
    (Monoid.exponent_eq_of_mulEquiv hEP).trans hfP.exponent_two⟩
  obtain ⟨g, hg, hga, hgu⟩ := U.property
  have hEI : E ≤ intersection D Y g := by
    intro e he
    obtain ⟨p, hp, rfl⟩ := he
    refine ⟨p.property, ?_⟩
    rw [map_fixer D Y ⟨g, Subgroup.centralizer_le_normalizer _ hg⟩]
    refine ⟨p.property.1, ?_⟩
    change (p : G) • (g • Y) = g • Y
    rw [hgu]
    exact congrArg (fun V : A => (V : D.Vertex)) (hU ⟨p, hp⟩)
  have hsl : sl2Join D Y U := hgu ▸
    inner_sl2Join_of_four_subgroup D Y hY ⟨g, hg⟩ hga E hEI hfE
  have hs2 : IsPGroup 2 (stabilizer (fixer D Y) (U : D.Vertex)) := by
    let f : stabilizer (fixer D Y) (U : D.Vertex) →* edgeFixer G Y (U : D.Vertex) := {
      toFun := fun u => ⟨u.val.val, u.val.property.2, u.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
    exact (sl2_fixer_isPGroup D Y U hsl).of_injective f
      (fun x y h => Subtype.ext (Subtype.ext (show x.val.val = y.val.val from
        congrArg (fun z : edgeFixer G Y (U : D.Vertex) => (z : G)) h)))
  have hFc : Nat.card (fixer D Y) = 60 := by
    rw [Nat.card_congr hF.some.toEquiv, nat_card_alternatingGroup]
    norm_num
  have hstab_le : Nat.card (stabilizer (fixer D Y) (U : D.Vertex)) ≤ 4 := by
    have hd := (stabilizer (fixer D Y) (U : D.Vertex)).card_subgroup_dvd_card
    rw [hFc] at hd
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hs2
    have hd4 : 2 ^ n ∣ 4 := by
      change 2 ^ n ∣ 2 ^ 2
      apply (Nat.dvd_prime_pow Nat.prime_two).mpr
      refine ⟨n, ?_, rfl⟩
      have hnle := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (by decide : 60 ≠ 0)).mp (hn ▸ hd)
      simpa only [show Nat.factorization 60 2 = 2 by decide +kernel] using hnle
    exact Nat.le_of_dvd (by decide) (hn.symm ▸ hd4)
  have hsub : orbit (fixer D Y) (U : D.Vertex) ⊆ innerSet D Y := by
    rintro W ⟨f, rfl⟩
    exact inner_fixer_smul_mem D Y hF f U.property
  have horbit : orbit (fixer D Y) (U : D.Vertex) = innerSet D Y := by
    apply Set.eq_of_subset_of_ncard_le hsub
    have hc := Nat.card_congr (orbitProdStabilizerEquivGroup (fixer D Y) (U : D.Vertex))
    rw [Nat.card_prod, hFc] at hc
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, hcard]
    nlinarith
  have hj (W : D.Vertex) (hW : W ∈ innerSet D Y) : sl2Join D Y W := by
    rw [← horbit] at hW
    obtain ⟨f, hf⟩ := hW
    change (f : G) • (U : D.Vertex) = W at hf
    have h := (sl2Join_smul_iff D (f : G) Y U).mpr hsl
    rwa [show (f : G) • Y = Y from f.property.2, hf] at h
  refine ⟨hj, ?_⟩
  intro V hV W hW
  rw [← horbit] at hV hW
  obtain ⟨f, hf⟩ := hV
  obtain ⟨k, hk⟩ := hW
  refine ⟨k * f⁻¹, ?_⟩
  change (f : G) • (U : D.Vertex) = V at hf
  change (k : G) • (U : D.Vertex) = W at hk
  rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_smul, ← hf, inv_smul_smul, hk]


/-- The full centralizer of the local A₅ is exactly the marked D₁₀.
A larger subgroup of the A₅ fixer would be the entire fixer. Its pure
four-group would then centralize a group of order sixty inside a group
of order 192, which is impossible. -/
theorem frame_double_centralizer {D : Seed G} (F : EdgeFrame D) :
    centralizer (F.K : Set G) = F.B := by
  have hF := InvolutionGeometry.Applications.edgeFixer_equiv D F.adjacent
  obtain ⟨eK⟩ := (InvolutionGeometry.Applications.edgeFrame_calculations D F).1
  have hKc : Nat.card F.K = 60 := by
    rw [Nat.card_congr eK.toEquiv, nat_card_alternatingGroup]
    norm_num
  have hFc : Nat.card (fixer D F.y) = 60 := by
    rw [Nat.card_congr hF.some.toEquiv, nat_card_alternatingGroup]
    norm_num
  have hCF : centralizer (F.K : Set G) ≤ fixer D F.y := by
    rw [fixer, edgeFixer_eq_centralizer_join_of_alternatingFive D D.base F.y hF]
    exact centralizer_le (F.endpoints_le hF)
  have hBC : F.B ≤ centralizer (F.K : Set G) := le_centralizer_iff.mp le_rfl
  have hne : centralizer (F.K : Set G) ≠ fixer D F.y := by
    intro he
    let P : Sylow 2 (fixer D F.y) := Classical.choice inferInstance
    let E : Subgroup G := (P : Subgroup (fixer D F.y)).map (fixer D F.y).subtype
    let e : E ≃* P := ((P : Subgroup (fixer D F.y)).equivMapOfInjective
      (fixer D F.y).subtype (fixer D F.y).subtype_injective).symm
    have hp := sylow_fixer_four D F.y hF P
    let hfE : IsKleinFour E := ⟨(Nat.card_congr e.toEquiv).trans hp.card_four,
      (Monoid.exponent_eq_of_mulEquiv e).trans hp.exponent_two⟩
    have hEF : E ≤ fixer D F.y := map_subtype_le _
    have hpure : ∀ t ∈ E, t ≠ 1 → IsConj D.z t := by
      intro t ht htn
      apply source_fixer_involutions D F.y F.adjacent (hEF ht)
      apply orderOf_eq_prime _ htn
      have hs := IsKleinFour.mul_self (⟨t, ht⟩ : E)
      simpa only [pow_two, Subgroup.coe_mul, Subgroup.coe_one] using congrArg Subtype.val hs
    obtain ⟨em⟩ := PureFourCentralizer.models D E hfE hpure
    have hKC : F.K ≤ centralizer (E : Set G) := le_centralizer_iff.mp (he ▸ hEF)
    have hd := card_dvd_of_le hKC
    rw [hKc, Nat.card_congr em.toEquiv] at hd
    have hm : Nat.card HeisenbergFour.Model = 192 := by
      rw [Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod,
        HeisenbergFour.normal_card, HeisenbergFour.complement_card]
    norm_num [hm] at hd
  let J := (centralizer (F.K : Set G)).subgroupOf (fixer D F.y)
  have hJc : Nat.card J = Nat.card (centralizer (F.K : Set G)) :=
    Nat.card_congr (subgroupOfEquivOfLe hCF).toEquiv
  have hten : 10 ∣ Nat.card J := by
    rw [hJc, ← F.card_B]
    exact card_dvd_of_le hBC
  have hprod := J.card_mul_index
  rw [hFc] at hprod
  have hi : J.index ∣ 6 := by
    obtain ⟨k, hk⟩ := hten
    refine ⟨k, ?_⟩
    nlinarith
  have hproper : J ≠ ⊤ := fun h => hne
    (le_antisymm hCF (subgroupOf_eq_top.mp h))
  have hi6 : J.index = 6 := by
    have hb := Nat.le_of_dvd (by decide : 0 < 6) hi
    have hnot : ¬ J.index ≤ 4 := by
      intro hsmall
      let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
        ⟨commutator_alternatingGroup_eq_top (by simp)⟩
      let : Group.IsPerfect (fixer D F.y) :=
        Group.IsPerfect.ofSurjective (f := hF.some.symm.toMonoidHom) hF.some.symm.surjective
      exact hproper (top_unique (le_of_isPerfect_of_index_le_four ⊤ J hsmall))
    have hn5 : J.index ≠ 5 := by intro he; norm_num [he] at hi
    omega
  apply (eq_of_le_of_card_ge hBC ?_).symm
  rw [← hJc, F.card_B]
  rw [hi6] at hprod
  omega


private theorem external_mem_outer (D : Seed G) (Y : D.Vertex)
    (hY : D.graph.Adj D.base Y) (U : D.Vertex)
    (hUX : D.graph.Adj D.base U) (hUY : D.graph.Adj Y U)
    (hout : ¬ U.val ≤ D.X ⊔ Y.val) : U ∈ outerSet D Y := by
  have hF := InvolutionGeometry.Applications.edgeFixer_equiv D hY
  rcases neighbor_cover D (InvolutionGeometry.Applications.fourSuborbits D)
    Y hY hF U hUX with h | h | h
  · exact (hout (endpointOrbit_le_join D Y U h)).elim
  · have hsl := (inner_source_orbit D Y hY).1 U h
    have hc1 := card_join_of_sl2Join D hsl
    have hc2 := card_join_of_adj D hUY
    omega
  · exact h

/-- A source local A₅ constructs an external triangle and its exact six-point
fixer orbit. The X-orbit has a unique vertex adjacent to the second endpoint. -/
theorem external_orbit_witness (D : Seed G) (Y : D.Vertex)
    (hY : D.graph.Adj D.base Y) :
    ∃ T : D.Vertex, T ∈ outerSet D Y ∧ D.graph.Adj Y T ∧
      Nat.card (orbit (fixer D Y) T) = 6 ∧
      (∃! W : D.Vertex, W ∈ orbit D.X T ∧ D.graph.Adj Y W) ∧
      ∃ K : Subgroup G, Nonempty (K ≃* alternatingGroup (Fin 5)) ∧
        D.X ⊔ Y.val ⊔ T.val = K := by
  have hF := InvolutionGeometry.Applications.edgeFixer_equiv D hY
  let F := edgeFrameOfAlternatingFixer D Y hY hF.some
  obtain ⟨eK⟩ := (InvolutionGeometry.Applications.edgeFrame_calculations D F).1
  have hXY : D.X ⊔ Y.val ≤ F.K := F.endpoints_le hF
  obtain ⟨_, T, _, hTK, _, ht, _, hgen, _⟩ :=
    AlternatingFiveGeometry.exists_two_triangles D F.K eK Y hY
      (le_sup_left.trans hXY) (le_sup_right.trans hXY)
  have hTY : D.graph.Adj Y T := by
    obtain ⟨k, hk, hk'⟩ := ht.1
    have h := D.preserves (k : G) hY
    rwa [hk, hk'] at h
  have hTX : D.graph.Adj D.base T := by
    obtain ⟨k, hk, hk'⟩ := ht.2
    have h := D.preserves (k : G) hY
    rw [hk, hk'] at h
    exact h.symm
  have houtT : ¬ T.val ≤ D.X ⊔ Y.val := by
    intro hle
    have hc := card_join_of_adj D hY
    have he : D.X ⊔ Y.val = F.K := (sup_eq_left.mpr hle).symm.trans hgen
    change Nat.card (D.X ⊔ Y.val : Subgroup G) = 12 at hc
    rw [he, Nat.card_congr eK.toEquiv, nat_card_alternatingGroup] at hc
    norm_num at hc
  have hTo := external_mem_outer D Y hY T hTX hTY houtT
  have hc : Nat.card (orbit (fixer D Y) T) = 6 := by
    obtain ⟨g, hg, _, he⟩ := hTo
    have hi : intersection D Y g = F.B := by
      rw [intersection_eq_triple_centralizer D Y hF ⟨g, hg⟩, he, hgen]
      exact frame_double_centralizer F
    have h := fixer_orbit_card_of_dihedral_intersection D Y hF ⟨g, hg⟩
      ⟨(MulEquiv.subgroupCongr hi).trans F.dihedral.some⟩
    rwa [he] at h
  have huq : ∃! W : D.Vertex, W ∈ orbit D.X T ∧ D.graph.Adj Y W := by
    obtain ⟨W, A, B, _, _, _, horb, hw, ha, hb⟩ :=
      partition_in_alternatingFive D F.K eK Y T hY hTX
        (le_sup_left.trans hXY) (le_sup_right.trans hXY) hTK
        (fun h => houtT (endpointOrbit_le_join D Y T h))
    refine ⟨W, ⟨by rw [horb]; simp, hw⟩, ?_⟩
    rintro Z ⟨hz, hZY⟩
    rw [horb] at hz
    rcases hz with he | he | he
    · exact he
    · have hs := card_join_of_a5Join D ha
      have hc := card_join_of_adj D (he ▸ hZY)
      omega
    · have he' : Z = B := he
      have hs := card_join_of_a5Join D hb
      have hc := card_join_of_adj D (he' ▸ hZY)
      omega
  exact ⟨T, hTo, hTY, hc, huq, F.K, ⟨eK⟩, hgen⟩

/-- All external common neighbors form one orbit of the actual pointwise
edge fixer. The source local A₅ constructs a six-element orbit, and its
three X-translates exhaust the eighteen outer vertices. -/
theorem external_common_transitive (D : Seed G) (Y : D.Vertex)
    (hY : D.graph.Adj D.base Y) (U V : D.Vertex)
    (hUX : D.graph.Adj D.base U) (hUY : D.graph.Adj Y U)
    (hVX : D.graph.Adj D.base V) (hVY : D.graph.Adj Y V)
    (houtU : ¬ U.val ≤ D.X ⊔ Y.val) (houtV : ¬ V.val ≤ D.X ⊔ Y.val) :
    ∃ f : fixer D Y, (f : G) • U = V := by
  obtain ⟨T, hTo, hTY, hc, huq, _⟩ := external_orbit_witness D Y hY
  have hUo := external_mem_outer D Y hY U hUX hUY houtU
  have hVo := external_mem_outer D Y hY V hVX hVY houtV
  obtain ⟨f, hf⟩ := outer_transporter_of_single_orbit D Y hY T U hTo hUo hTY hUY hc huq
  obtain ⟨k, hk⟩ := outer_transporter_of_single_orbit D Y hY T V hTo hVo hTY hVY hc huq
  refine ⟨k * f⁻¹, ?_⟩
  rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_smul, ← hf, inv_smul_smul, hk]

/-- Every outer triple lies in a literal A₅ subgroup. Exhaustion by the
three X-translates of the six-point fixer orbit constructs this subgroup. -/
theorem outer_local_model (D : Seed G) (Y : D.Vertex)
    (hY : D.graph.Adj D.base Y) (U : D.Vertex) (hU : U ∈ outerSet D Y) :
    ∃ K : Subgroup G, Nonempty (K ≃* alternatingGroup (Fin 5)) ∧
      D.X ⊔ Y.val ⊔ U.val ≤ K := by
  obtain ⟨T, hTo, hTY, hc, huq, K, ⟨eK⟩, hK⟩ := external_orbit_witness D Y hY
  obtain ⟨x, f, hf⟩ := outer_decomposition_of_single_orbit D Y hY T U hTo hU hTY hc huq
  let K' := K.map (MulAut.conj (f : G)).toMonoidHom
  have hXY : D.X ⊔ Y.val ≤ K' := by
    have hm := Subgroup.map_mono (show D.base.val ⊔ Y.val ≤ K from
      le_sup_left.trans_eq hK) (f := (MulAut.conj (f : G)).toMonoidHom)
    rwa [Subgroup.map_sup, ← D.smul_val, ← D.smul_val,
      show (f : G) • D.base = D.base from f.property.1,
      show (f : G) • Y = Y from f.property.2] at hm
  have ht : ((f : G) • T).val ≤ K' := by
    rw [D.smul_val]
    exact Subgroup.map_mono (le_sup_right.trans_eq hK)
  have hu : U.val ≤ K' := by
    rw [← hf]
    exact conj_smul_le_of_le ht (⟨x, hXY ((le_sup_left : D.X ≤ D.X ⊔ Y.val) x.property)⟩ : K')
  exact ⟨K', ⟨(K.equivMapOfInjective _ (MulAut.conj (f : G)).injective).symm.trans eK⟩,
    sup_le hXY hu⟩

/-- The source outer orbit has one A₄ join and two A₅ joins under X.
All intersection and local-model assumptions are discharged. -/
theorem outer_source_partition (D : Seed G) (Y : D.Vertex)
    (hY : D.graph.Adj D.base Y) (U : D.Vertex) (hU : U ∈ outerSet D Y) :
    ∃ W A B : D.Vertex, W ≠ A ∧ W ≠ B ∧ A ≠ B ∧
      orbit D.X U = {W, A, B} ∧ D.graph.Adj Y W ∧ a5Join D Y A ∧ a5Join D Y B ∧
      ∀ V ∈ orbit D.X U, D.graph.Adj D.base V := by
  have hF := InvolutionGeometry.Applications.edgeFixer_equiv D hY
  have hUX : D.graph.Adj D.base U := by
    obtain ⟨g, hg, _, rfl⟩ := hU
    have h := D.preserves g hY
    rwa [normalizer_fixes_base D ⟨g, hg⟩] at h
  obtain ⟨K, ⟨eK⟩, hK⟩ := outer_local_model D Y hY U hU
  obtain ⟨W, A, B, hWA, hWB, hAB, horb, hw, ha, hb⟩ :=
    partition_in_alternatingFive D K eK Y U hY hUX
      (le_sup_left.trans (le_sup_left.trans hK))
      (le_sup_right.trans (le_sup_left.trans hK)) (le_sup_right.trans hK)
      (outer_not_endpointOrbit D Y U hF hU)
  exact ⟨W, A, B, hWA, hWB, hAB, horb, hw, ha, hb,
    fun _ hv => orbit_neighbors D hUX hv⟩

/-- The inner range is precisely the fifteen neighbors making an SL₂(3) join. -/
theorem innerSet_eq_sl2_neighbors (D : Seed G) (Y : D.Vertex)
    (hY : D.graph.Adj D.base Y) :
    innerSet D Y = {U | D.graph.Adj D.base U ∧ sl2Join D Y U} := by
  ext U
  constructor
  · intro hU
    refine ⟨?_, (inner_source_orbit D Y hY).1 U hU⟩
    obtain ⟨g, hg, _, rfl⟩ := hU
    have h := D.preserves g hY
    rwa [normalizer_fixes_base D ⟨g, Subgroup.centralizer_le_normalizer _ hg⟩] at h
  · rintro ⟨hUX, hsl⟩
    have hF := InvolutionGeometry.Applications.edgeFixer_equiv D hY
    rcases neighbor_cover D (InvolutionGeometry.Applications.fourSuborbits D)
      Y hY hF U hUX with he | hi | ho
    · have hc := Subgroup.card_le_of_le
        (sup_le (show Y.val ≤ D.X ⊔ Y.val from le_sup_right)
          (endpointOrbit_le_join D Y U he))
      have hs := card_join_of_sl2Join D hsl
      have ha := card_join_of_adj D hY
      change Nat.card (Y.val ⊔ U.val : Subgroup G) ≤ Nat.card (D.X ⊔ Y.val : Subgroup G) at hc
      change Nat.card (D.X ⊔ Y.val : Subgroup G) = 12 at ha
      omega
    · exact hi
    · obtain ⟨W, A, B, _, _, _, horb, hw, ha, hb, _⟩ := outer_source_partition D Y hY U ho
      have hm := mem_orbit_self (M := D.X) U
      rw [horb] at hm
      have hs := card_join_of_sl2Join D hsl
      rcases hm with he | he | he
      · have hc := card_join_of_adj D (he.symm ▸ hw)
        omega
      · have hc := card_join_of_a5Join D (he.symm ▸ ha)
        omega
      · have he' : U = B := he
        have hc := card_join_of_a5Join D (he'.symm ▸ hb)
        omega

/-- The exact fifteen-point intersection number in source 47.6(1). -/
theorem source_sl2_neighbors_card (D : Seed G) (Y : D.Vertex)
    (hY : D.graph.Adj D.base Y) :
    {U | D.graph.Adj D.base U ∧ sl2Join D Y U}.ncard = 15 := by
  obtain ⟨H⟩ := source_calculation D
  rw [← innerSet_eq_sl2_neighbors D Y hY, ← Nat.card_coe_set_eq]
  exact innerSet_card D H Y (InvolutionGeometry.Applications.edgeFixer_equiv D hY)

/-- There are six outer common neighbors, counted in the actual fixer orbit. -/
theorem outer_common_neighbors_card (D : Seed G) (Y : D.Vertex)
    (hY : D.graph.Adj D.base Y) :
    {U | U ∈ outerSet D Y ∧ D.graph.Adj Y U}.ncard = 6 := by
  obtain ⟨T, hTo, hTY, hc, huq, _⟩ := external_orbit_witness D Y hY
  have hF := InvolutionGeometry.Applications.edgeFixer_equiv D hY
  have he : {U | U ∈ outerSet D Y ∧ D.graph.Adj Y U} = orbit (fixer D Y) T := by
    ext U
    constructor
    · rintro ⟨hu, ha⟩
      exact outer_transporter_of_single_orbit D Y hY T U hTo hu hTY ha hc huq
    · rintro ⟨f, rfl⟩
      refine ⟨outer_smul_mem D Y ⟨f, fixer_le_localCentralizer D Y hF f.property⟩ hTo, ?_⟩
      have h := D.preserves (f : G) hTY
      rwa [show (f : G) • Y = Y from f.property.2] at h
  rw [he, ← Nat.card_coe_set_eq]
  exact hc

/-- The A₅-join neighbors are the other twelve vertices of the outer range. -/
theorem source_a5_neighbors_card (D : Seed G) (Y : D.Vertex)
    (hY : D.graph.Adj D.base Y) :
    {U | D.graph.Adj D.base U ∧ a5Join D Y U}.ncard = 12 := by
  have hF := InvolutionGeometry.Applications.edgeFixer_equiv D hY
  let C : Set D.Vertex := {U | U ∈ outerSet D Y ∧ D.graph.Adj Y U}
  have he : {U | D.graph.Adj D.base U ∧ a5Join D Y U} = outerSet D Y \ C := by
    ext U
    constructor
    · rintro ⟨hu, ha⟩
      have hc := card_join_of_a5Join D ha
      have houter : U ∈ outerSet D Y := by
        rcases neighbor_cover D (InvolutionGeometry.Applications.fourSuborbits D)
          Y hY hF U hu with he | hi | ho
        · have hb := Subgroup.card_le_of_le
            (sup_le (show Y.val ≤ D.X ⊔ Y.val from le_sup_right)
              (endpointOrbit_le_join D Y U he))
          have hj := card_join_of_adj D hY
          change Nat.card (Y.val ⊔ U.val : Subgroup G) ≤ Nat.card (D.X ⊔ Y.val : Subgroup G) at hb
          change Nat.card (D.X ⊔ Y.val : Subgroup G) = 12 at hj
          omega
        · have hs := card_join_of_sl2Join D ((inner_source_orbit D Y hY).1 U hi)
          omega
        · exact ho
      refine ⟨houter, ?_⟩
      intro h
      have hj := card_join_of_adj D h.2
      omega
    · rintro ⟨hu, hn⟩
      obtain ⟨W, A, B, _, _, _, horb, hw, ha, hb, hbase⟩ := outer_source_partition D Y hY U hu
      have hm := mem_orbit_self (M := D.X) U
      refine ⟨hbase U hm, ?_⟩
      rw [horb] at hm
      rcases hm with he | he | he
      · exact (hn ⟨hu, he.symm ▸ hw⟩).elim
      · exact he.symm ▸ ha
      · have he' : U = B := he
        exact he'.symm ▸ hb
  obtain ⟨H⟩ := source_calculation D
  have hc : C.ncard = 6 := outer_common_neighbors_card D Y hY
  rw [he, Set.ncard_sdiff (show C ⊆ outerSet D Y from fun _ h => h.1), hc,
    ← Nat.card_coe_set_eq, outerSet_card D H Y hF]

/-- The corrected adjacent common-neighbor count, forced by the source's
36, 15 and 12 incidence counts. The printed value 18 in 47.6(3) is erroneous. -/
theorem source_common_neighbors_card (D : Seed G) (Y : D.Vertex)
    (hY : D.graph.Adj D.base Y) :
    {U | D.graph.Adj D.base U ∧ D.graph.Adj Y U}.ncard = 8 :=
  (InvolutionGeometry.Applications.fourSuborbits D).common_neighbors_card_of_intersections
    hY (source_sl2_neighbors_card D Y hY) (source_a5_neighbors_card D Y hY)

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.EdgeConfigurations
