module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.StrictSmallActorCentralizer
public import Theory.GroupTheory.CoprimeInvolutiveSupplement
public import Theory.GroupTheory.WeakBNPair.RegularTree.PathMidpointCoordinates

/-!
# The chosen strict reflection belongs to the actual two-root actor

The original full Cartan has no fixed points in the midpoint core. A chosen
apartment reflection normalizes the two-root actor and that Cartan. The
coprime binary-coset argument therefore puts the reflection in the actual
actor, even when its own two-core is nontrivial. Its action on the whole
supported twelve-path is retained, along with centralization of C∩U.

No natural-kernel, trivial-core, reflection or exchange premise is assumed.
Source: DGS, Groups and Graphs (1985), (14.2)–(14.3), pp.210–212;
(14.9) and (14.17), pp.215–216,221.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam SimpleGraph SimpleGraph.Walk
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
open scoped MatrixGroups Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
open Reduction NoncommutingProfile OriginalExtension SuzukiContainment CommutingNontrivial
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable (h : HypothesisF11 L S) {u : Vertex (reducedFamily L S)}
  (hc : IsCriticalPair (reducedFamily L S) (base (reducedFamily L S) false) u)
  (hne : ⁅Z (reducedFamily L S) (base (reducedFamily L S) false),
    Z (reducedFamily L S) u⁆ ≠ ⊥)
  (hb : b (reducedFamily L S) = 2)
  (hβu : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) true) u)
  (hns : ¬ Group.IsSolvable (parabolic L S 0))
  {n : ℕ} (hlinear : ClassicalGroup.IsPSL (L 0 ⧸ pCore 2 (L 0)) 2 (2^n))

local notation "F" => reducedFamily L S
local notation "A" => reducedAmalgam L S
local notation "T" => Universal.cosetFamily A
local notation "G₀" => Reduction.G₀ L S
variable {a b : SourceVertex (reducedAmalgam L S)}
    (p : (sourceGraph (reducedAmalgam L S)).Walk a b)
    (hp : p.IsPath) (hl : p.length = 12)
    (hT : ∀ z ∈ p.support,
      z ∈ strictSourceApartment h hc hne hb hβu hns hlinear)

include h hc hne hb hβu hns hlinear hl hT

/-- A midpoint involution normalizing the full chosen Cartan centralizes
its full local permutation-kernel part. -/
theorem strict_source_reflection_kernel
    (x : (A).Universal) (hx2 : x*x=1)
    (hxC : x∈normalizer (cartan (chosenCartans h) : Set (A).Universal))
    (hxfix : x • p.getVert 6=p.getVert 6) :
    ∀ k∈cartan (chosenCartans h) ⊓ (U F ((bOne_tree_cover h).vertex (p.getVert 6))).comap
      (bOne_tree_map h), Commute x k := by
  let c := chosenCartans h
  let r := strictSourceReflections h hc hne hb hβu hns hlinear
  let t := r.t
  have htfix := r.fixes
  have htmove := r.moves
  have htsq := r.square
  have htnorm := r.normalizes
  let φ := bOne_tree_map h
  let cov := bOne_tree_cover h
  let C := (cartan c).map φ
  let v := cov.vertex (p.getVert 6)
  let w := cov.vertex (p.getVert 7)
  let J := graphLocalGroup F v
  let _ : ∀ i, Finite (F i) := finite_endpoints (reduced_triple h)
  have hvw : (graph F).Adj v w := cov.hom.map_adj (p.adj_getVert_succ (by omega))
  obtain ⟨K,fK,finK,chK,hK,e,_⟩ :=
    strict_source_small_actor_linear_quotients h hc hne hb hβu hns hlinear
  let _ := fK
  let _ := finK
  let _ := chK
  have hfour := hK v.type
  have hJU : J ⊓ U F v=Q F v := CommutingTrivial.nonbinary_local_kernel_intersection
    (reduced_triple h) (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hvw (e v) hfour
  have ho : Odd (Nat.card C) := (Nat.coprime_two_left.mp (cartan_odd c)).of_dvd_nat
    ((cartan c).card_map_dvd φ)
  let _ : Finite (Q F v) := Finite.of_injective (inclusion (Q_le_stabilizer F v))
    (inclusion_injective _)
  have hdis : Disjoint C (Q F v) := by
    have hpQ : IsPGroup 2 (Q F v) := isPGroup_pCoreIn 2 _
    obtain ⟨r,hr⟩ := hpQ.exists_card_eq
    exact disjoint_of_coprime_natCard (by rw [hr]; exact ho.coprime_two_right.pow_right r)
  have huv : φ x∈stabilizer F v := by
    change φ x • cov.vertex (p.getVert 6)=_
    rw [←cov.vertex_smul,hxfix]
  have huJ : φ x∈J := by
    have hpow : φ x^(2^1)=1 := by rw [pow_one,pow_two,←map_mul,hx2,map_one]
    exact pGroup_le_sylowGenerated (stabilizer F v) (zpowers (φ x))
      (zpowers_le.mpr huv) (IsPGroup.of_card_dvd_pow (by
        rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hpow)) (mem_zpowers _)
  have hunC : φ x∈normalizer (C : Set G₀) :=
    (cartan c).le_normalizer_map φ (mem_map_of_mem φ hxC)
  intro k hk
  have hkfix : k • p.getVert 6=p.getVert 6 :=
    reflectionApartment_fixed c t htnorm k hk.1 _ (hT _ (p.getVert_mem_support 6))
  have hkv : φ k∈stabilizer F v := by
    change φ k • cov.vertex (p.getVert 6)=_
    rw [←cov.vertex_smul,hkfix]
  have hkC : φ k∈C := mem_map_of_mem φ hk.1
  have hkU : φ k∈U F v := hk.2
  let z := φ x*φ k*(φ x)⁻¹*(φ k)⁻¹
  have hzC : z∈C := C.mul_mem ((mem_normalizer_iff.mp hunC _).mp hkC) (C.inv_mem hkC)
  have hzJ : z∈J := by
    have hh := (mem_normalizer_iff.mp (sylowGenerated_normalized _ hkv) _).mp (J.inv_mem huJ)
    have he : z=φ x*(φ k*(φ x)⁻¹*(φ k)⁻¹) := by dsimp [z]; group
    rw [he]
    exact J.mul_mem huJ hh
  have hzU : z∈U F v := (U F v).mul_mem
    ((mem_normalizer_iff.mp (stabilizer_le_normalizer_ballKernel F v 1 huv) _).mp hkU)
      ((U F v).inv_mem hkU)
  have hz1 : z=1 := disjoint_def.mp hdis hzC (hJU.le ⟨hzJ,hzU⟩)
  have hcommute : φ x*φ k=φ k*φ x :=
    mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hz1)
  have hfixuk : (x*k) • p.getVert 6=p.getVert 6 := by rw [mul_smul,hkfix,hxfix]
  have hfixku : (k*x) • p.getVert 6=p.getVert 6 := by rw [mul_smul,hxfix,hkfix]
  have he := (cov.stabilizerEquiv (p.getVert 6)).injective
    (a₁ := ⟨x*k,hfixuk⟩) (a₂ := ⟨k*x,hfixku⟩)
    (Subtype.ext (show φ (x*k)=φ (k*x) by simpa only [map_mul] using hcommute))
  exact congrArg Subtype.val he

include hp

/-- A chosen-Cartan involution reversing the strict twelve-path belongs
to its actual two-root actor, including the nontrivial own-core case. -/
theorem strict_source_reflection_mem_actor
    (x : (A).Universal) (hx2 : x*x=1)
    (hxC : x∈normalizer (cartan (chosenCartans h) : Set (A).Universal))
    (hrev : ∀ j≤12, x • p.getVert j=p.getVert (12-j)) :
    x∈halfPathActor (X := (A).Universal) p 6 := by
  let c := chosenCartans h
  let r := strictSourceReflections h hc hne hb hβu hns hlinear
  let t := r.t
  have htfix := r.fixes
  have htmove := r.moves
  have htsq := r.square
  have htnorm := r.normalizes
  let φ := bOne_tree_map h
  let cov := bOne_tree_cover h
  let C := (cartan c).map φ
  let D := halfPathActor (X := (A).Universal) p 6
  let M := D.map φ
  let v := cov.vertex (p.getVert 6)
  let w := cov.vertex (p.getVert 7)
  let J := graphLocalGroup F v
  let _ : ∀ i, Finite (F i) := finite_endpoints (reduced_triple h)
  let _ := cartan_abelian h c
  let _ : IsMulCommutative C := inferInstanceAs (IsMulCommutative ((cartan c).map φ))
  have hvw : (graph F).Adj v w := cov.hom.map_adj (p.adj_getVert_succ (by omega))
  obtain ⟨K,fK,finK,chK,hK,e,hactors⟩ :=
    strict_source_small_actor_linear_quotients h hc hne hb hβu hns hlinear
  obtain ⟨_,_,hcover,_⟩ := hactors p hp hl hT
  have hfix (k) (hk : k∈cartan c) (j : ℕ) : k • p.getVert j=p.getVert j :=
    reflectionApartment_fixed c t htnorm k hk _ (hT _ (p.getVert_mem_support j))
  have hDn : cartan c ≤ normalizer (D : Set (A).Universal) := by
    intro k hk
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (pathRoot (X := (A).Universal) (p.drop 6) ⊔
      pathRoot (X := (A).Universal) (p.take 6)).map _ = _
    rw [Subgroup.map_sup]
    have hr := pathRoot_map_conj (p.drop 6) (p.drop 6) k rfl
      (fun j _ => by rw [drop_getVert]; exact hfix k hk _)
    have ht := pathRoot_map_conj (p.take 6) (p.take 6) k rfl
      (fun j _ => by rw [take_getVert]; exact hfix k hk _)
    exact congrArg₂ (fun R V : Subgroup (A).Universal => R ⊔ V) hr ht
  have hCD : C ≤ normalizer (M : Set G₀) :=
    (map_mono hDn).trans
      (D.le_normalizer_map φ)
  have hCP : C ⊓ J ≤ M := (strict_source_small_actor_cartan_le
    h hc hne hb hβu hns hlinear p hp hl hT).1
  have hCE : C ≤ stabilizer F v ⊓ stabilizer F w := by
    rintro _ ⟨k,hk,rfl⟩
    constructor
    · change φ k • cov.vertex (p.getVert 6)=_
      rw [←cov.vertex_smul,reflectionApartment_fixed c t htnorm k hk _
        (hT _ (p.getVert_mem_support 6))]
    · change φ k • cov.vertex (p.getVert 7)=_
      rw [←cov.vertex_smul,reflectionApartment_fixed c t htnorm k hk _
        (hT _ (p.getVert_mem_support 7))]
  let E := F false ⊓ F true
  let W := (twoGroup L S).map φ
  have hmapE : (originalMiddle A).map φ=E := by
    rw [show originalMiddle A=T false ⊓ T true from
      (Universal.overlap_eq A (inclusion_injective (commonBorel_le_parabolic 0))
        (inclusion_injective (commonBorel_le_parabolic 1))).symm]
    exact cov.map_inf
  have hC0 : C ≤ E := hmapE ▸ map_mono (cartan_le c)
  have hW0 : W ≤ E := hmapE ▸ map_mono (twoGroup_le (L := L) (S := S))
  have hWn : E ≤ normalizer (W : Set G₀) := by
    rw [←hmapE]
    exact (map_mono (twoGroup_normalized h)).trans ((twoGroup L S).le_normalizer_map φ)
  have hWcore : W ≤ E.pCoreIn 2 :=
    le_pCoreIn_of_normalizes ((twoGroup_isTwo h).map φ) hW0 hWn
  have ho : Odd (Nat.card C) := (Nat.coprime_two_left.mp (cartan_odd c)).of_dvd_nat
    ((cartan c).card_map_dvd φ)
  let _ : Finite E := Finite.of_injective (inclusion (show E ≤ F false from inf_le_left))
    (inclusion_injective _)
  let _ : Finite (E.pCoreIn 2) := Finite.of_injective (inclusion (pCoreIn_le 2 E))
    (inclusion_injective _)
  have hd0 : Disjoint C (E.pCoreIn 2) := by
    obtain ⟨r,hr⟩ := (isPGroup_pCoreIn 2 E).exists_card_eq
    exact disjoint_of_coprime_natCard (by rw [hr]; exact ho.coprime_two_right.pow_right r)
  have hg0 : C ⊔ E.pCoreIn 2=E := by
    apply le_antisymm (sup_le hC0 (pCoreIn_le 2 E))
    have he := congrArg (Subgroup.map φ) (factorization c)
    rw [Subgroup.map_sup,hmapE] at he
    exact he.symm.le.trans (sup_le (hWcore.trans le_sup_right) le_sup_left)
  have hEbase : E=stabilizer F (base F false) ⊓ stabilizer F (base F true) := by
    rw [show stabilizer F (base F false)=F false from Subgroup.CosetGeometry.stabilizer_base F false,
      show stabilizer F (base F true)=F true from Subgroup.CosetGeometry.stabilizer_base F true]
  have hbase : (graph F).Adj (base F false) (base F true) :=
    ⟨by change false≠true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  obtain ⟨hd,hg⟩ := CommutingTrivial.path_cartan_complement_at_edge (reduced_triple h)
    hbase hvw C (hEbase ▸ hC0) hCE ho (hEbase ▸ hd0) (hEbase ▸ hg0)
  have hfixed : Q F v ⊓ centralizer (C : Set G₀)=⊥ :=
    original_bTwo_strict_cartan_core_centralizer h hc hne hb hβu hns hlinear
      hvw C hCE ho hd hg
  have huv : x • p.getVert 6=p.getVert 6 := hrev 6 (by decide)
  have hφuv : φ x∈stabilizer F v := by
    change φ x • cov.vertex (p.getVert 6)=_
    rw [←cov.vertex_smul,huv]
  have hφu2 : φ x*φ x=1 := by rw [←map_mul,hx2,map_one]
  have hφuJ : φ x∈J := by
    have hpow : φ x^(2^1)=1 := by simpa only [pow_one,pow_two] using hφu2
    exact pGroup_le_sylowGenerated (stabilizer F v) (zpowers (φ x))
      (zpowers_le.mpr hφuv) (IsPGroup.of_card_dvd_pow (by
        rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hpow)) (mem_zpowers _)
  have hunD : x∈normalizer (D : Set (A).Universal) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (pathRoot (X := (A).Universal) (p.drop 6) ⊔ pathRoot (X := (A).Universal) (p.take 6)).map _=_
    rw [Subgroup.map_sup]
    obtain ⟨ha,hb⟩ := pathRoot_halves_reflection p 6 hl x hrev
    exact (congrArg₂ (fun R V : Subgroup (A).Universal => R ⊔ V) hb ha).trans
      (sup_comm _ _)
  let _ : Finite (Q F v) := Finite.of_injective (inclusion (Q_le_stabilizer F v))
    (inclusion_injective _)
  let _ : Finite C := Finite.of_injective (inclusion (hCE.trans inf_le_left))
    (inclusion_injective _)
  have huM : φ x∈M := involution_mem_supplement_of_coprime_cartan_control M (Q F v) C J
    (isPGroup_pCoreIn 2 _) ho (halfPathActor_map_le_local h p 6 hl) hcover
    ((sylowGenerated_le _).trans (stabilizer_normalizes_Q F v)) hCD
    ((hCE.trans inf_le_left).trans (stabilizer_normalizes_Q F v)) hCP hfixed (φ x) hφuJ
    (D.le_normalizer_map φ (mem_map_of_mem φ hunD))
    ((cartan c).le_normalizer_map φ (mem_map_of_mem φ hxC)) hφu2
  obtain ⟨d,hd,hdu⟩ := huM
  have hdv := halfPathActor_le_midpoint_stabilizer hl hd
  have he := (cov.stabilizerEquiv (p.getVert 6)).injective
    (a₁ := ⟨d,hdv⟩) (a₂ := ⟨x,huv⟩) (Subtype.ext hdu)
  have hdu' : d=x := congrArg Subtype.val he
  exact hdu' ▸ hd

/-- Every supported strict twelve-path has a reversing involution inside
its own two-root actor and the original reflection group. No reflection or
kernel hypothesis is supplied by the caller. -/
theorem strict_source_small_actor_reflection :
    ∃ x∈halfPathActor (X := (A).Universal) p 6,
      x∈reflectionGroup (chosenCartans h)
        (strictSourceReflections h hc hne hb hβu hns hlinear).t ∧
      x∈normalizer (cartan (chosenCartans h) : Set (A).Universal) ∧
      x*x=1 ∧ (∀ j≤12, x • p.getVert j=p.getVert (12-j)) ∧
      ∀ k∈cartan (chosenCartans h) ⊓
        (U F ((bOne_tree_cover h).vertex (p.getVert 6))).comap (bOne_tree_map h),
        Commute x k := by
  let c := chosenCartans h
  let r := strictSourceReflections h hc hne hb hβu hns hlinear
  let t := r.t
  have htfix := r.fixes
  have htmove := r.moves
  have htsq := r.square
  have htnorm := r.normalizes
  let d := strictSourceSmallActorGeometry h hc hne hb hβu hns hlinear
  have hpath : BasedPathTransitive (X := (A).Universal) (sourceGraph A) 7 := d.transitive
  have hthick := d.thick
  let ρ := pathRoots h c 6 (by decide) t htfix htmove htsq htnorm hpath hthick
  let N := reflectionGroup c t
  have ha := pathRoots_a h c 6 (by decide) t htfix htmove htsq htnorm hpath hthick
  have hb' := pathRoots_b h c 6 (by decide) t htfix htmove htsq htnorm hpath hthick
  have hlift := reflection_mem_apartmentGroup c ρ
  have hnorm := reflectionGroup_normalizes c t htnorm
  have hline := cartanApartment_noBranching A N (cartan c) ρ ha hb' hlift
    (cartan_le c) hnorm le_rfl htsq
    (inclusion_injective (commonBorel_le_parabolic 0))
    (inclusion_injective (commonBorel_le_parabolic 1))
  obtain ⟨g,hg,i,hgv,hgw⟩ := cartanApartment_edge_coordinates A N ρ ha hb' hlift hline
    (hT _ (p.getVert_mem_support 6)) (hT _ (p.getVert_mem_support 7))
    (p.adj_getVert_succ (by omega))
  let u := g*t i*g⁻¹
  have huu : u*u=1 := by
    calc
      _ = g*(t i*t i)*g⁻¹ := by dsimp [u]; group
      _ = 1 := by rw [htsq,mul_one,mul_inv_cancel]
  have huN : u∈N := N.mul_mem (N.mul_mem hg (reflectionGroup_mem c t i)) (N.inv_mem hg)
  have hufix : u • p.getVert 6=p.getVert 6 := by
    rw [←hgv]
    change (g*t i*g⁻¹) • (g • base T i)=g • base T i
    rw [mul_smul,mul_smul,inv_smul_smul,htfix]
  have humove : u • p.getVert 7≠p.getVert 7 := by
    rw [←hgw]
    change (g*t i*g⁻¹) • (g • base T (!i))≠g • base T (!i)
    rw [mul_smul,mul_smul,inv_smul_smul]
    exact fun he => htmove i ((MulAction.toPerm g).injective he)
  have hrev := reverses_path_of_moves_midpoint_neighbor (source_action A) hline p hp 6
    (by decide) hl hT u huu (fun _ hz => cartanApartment_preserves A N huN hz) hufix humove
  have huD := strict_source_reflection_mem_actor h hc hne hb hβu hns hlinear
    p hp hl hT u huu (hnorm huN) hrev
  refine ⟨u,huD,huN,hnorm huN,huu,hrev,?_⟩
  exact strict_source_reflection_kernel h hc hne hb hβu hns hlinear
    p hl hT u huu (hnorm huN) hufix

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
