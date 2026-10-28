module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.OppositeSeedOmega
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.RankOnePairSplitting

/-!
# Descending the center-pair splitting and eliminating its complement

Conjugation by the center pair moves the alpha vertices and is trivial
on Q_beta/V. Factoring an adjacent-core element into the first seed and
the opposite core proves Q_alpha intersect Q_beta = (Z_alpha intersect
Q_beta) D, where D is the intersection of the two alpha cores.

Consequently the existing splitting modulo D descends to the exact further
quotient by Q_alpha intersect Q_beta. Its factors are the opposite seed
and the image of the odd actor's centralizer; their multiplication is the
explicit direct-product equivalence. On the source Cartan-fixed triple,
OppositeSeedOmega identifies the entire first omega subgroup with the first
factor. Every nontrivial finite two-group has an involution, so the second
factor is trivial. Lifting proves (11.3)(h), with every original alpha
and beta model retained. No Omega_1(Q_beta/D) assertion is used.

ReducedPairCoreSpan supplies the actual source-path, original-completion
and elementary-profile applications. The source (11.4) edge-core product,
later profiles and final earlier-source discharge remain separate duties.
Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(11.3)(h), printed pp.170--171, using (11.3)(a,b) and (6.7).
-/

public noncomputable section
open Subgroup
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The exact adjacent-core intersection modulo the two-alpha-core kernel.
The proof uses the center-pair conjugator and its displacement in V. -/
theorem source_pair_adjacent_core_intersection
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b))) :
    Q (family P) a ⊓ Q (family P) b =
      (Z (family P) a ⊓ Q (family P) b) ⊔ (Q (family P) a ⊓ Q (family P) c) := by
  let E := Z (family P) a ⊓ Q (family P) b
  let I := Q (family P) a ⊓ Q (family P) b
  let Ic := Q (family P) c ⊓ Q (family P) b
  let D := Q (family P) a ⊓ Q (family P) c
  let V := pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b)
  have hab := source_critical_one_adjacent hc hb
  have hEQ : E ≤ Q (family P) a := inf_le_left.trans ((source_Z_Q_U h a).1.trans (map_subtype_le _))
  have hDQ : D ≤ Q (family P) b := source_rankOne_pair_core_le_beta h hB d hab hbc hac Mb
  have hn : E ≤ normalizer (Ic : Set G) := inf_le_right.trans
    ((le_inf (source_adjacent_core_normalizes_core h hbc) (Q (family P) b).le_normalizer).trans
      inf_normalizer_le_normalizer_inf)
  obtain ⟨g,hg,hga⟩ := source_rankOne_center_pair_moves h hB d hc hb hbc Mb
  have hgb : g • b = b := by
    have hh := source_pair_actor_map h hB d hc hb hbc hac Mb
    obtain ⟨hHK,_⟩ := hh
    exact d.local_le b (hHK (mem_sup_left hg))
  have hImap : I.map (MulAut.conj g).toMonoidHom = Ic := by
    dsimp only [I,Ic]
    rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective,←Q_translate,←Q_translate,hga,hgb]
  have hIV : I ≤ E ⊔ Ic := by
    intro x hx
    have hy : g*x*g⁻¹ ∈ Ic := hImap ▸ mem_map_of_mem (MulAut.conj g).toMonoidHom hx
    have hcomm : ⁅x,g⁆ ∈ V := (source_pair_core_normalizers h hab hbc).2.2.2
      (commutator_mem_commutator hx.2 hg)
    have hV : V ≤ E ⊔ Ic := sup_le le_sup_left
      ((le_inf (inf_le_left.trans ((source_Z_Q_U h c).1.trans (map_subtype_le _))) inf_le_right).trans le_sup_right)
    have hh := (E ⊔ Ic).mul_mem (hV hcomm) (mem_sup_right hy)
    convert hh using 1; group
  apply le_antisymm
  · intro x hx
    have hp : x ∈ (E : Set G) * (Ic : Set G) := by
      rw [←coe_mul_of_left_le_normalizer_right E Ic hn]
      exact hIV hx
    obtain ⟨e,he,z,hz,rfl⟩ := hp
    have hzQa : z ∈ Q (family P) a := by
      have hh := (Q (family P) a).mul_mem ((Q (family P) a).inv_mem (hEQ he)) hx.1
      simpa only [inv_mul_cancel_left] using hh
    exact mul_mem (mem_sup_left he) (mem_sup_right ⟨hzQa,hz.1⟩)
  · exact sup_le (le_inf hEQ inf_le_right) (le_inf inf_le_left hDQ)


/-- The pair splitting descends to the further quotient by the adjacent-core
intersection, with the opposite seed and complementary factor still literal images. -/
theorem source_pair_further_split_images {K : Type*} [Group K]
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (π : Q (family P) b →* K) (hπ : Function.Surjective π)
    (hker : π.ker = (Q (family P) a ⊓ Q (family P) b).subgroupOf (Q (family P) b))
    (y : G) (hy : y ∈ Z (family P) a ⊔ Z (family P) c)
    (hsplit : Q (family P) b =
      pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b) ⊔
        (Q (family P) b ⊓ centralizer (zpowers y : Set G)))
    (hint : pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b) ⊓
      centralizer (zpowers y : Set G) = Z (family P) a ⊓ Z (family P) c) :
    let F := Z (family P) c ⊓ Q (family P) b
    let A := (F.subgroupOf (Q (family P) b)).map π
    let C := ((Q (family P) b ⊓ centralizer (zpowers y : Set G)).subgroupOf (Q (family P) b)).map π
    IsElementaryAbelian 2 A ∧ Disjoint A C ∧
      ∃ e : A × C ≃* K, ∀ x z, e (x,z) = (x : K) * (z : K) := by
  let Q₀ := Q (family P) b
  let E := Z (family P) a ⊓ Q₀
  let F := Z (family P) c ⊓ Q₀
  let V := pairSpan (Z (family P) a) (Z (family P) c) Q₀
  let D := Q (family P) a ⊓ Q (family P) c
  let I := Q (family P) a ⊓ Q₀
  let C₀ := Q₀ ⊓ centralizer (zpowers y : Set G)
  let A₀ := F.subgroupOf Q₀
  let B₀ := (E ⊔ C₀).subgroupOf Q₀
  have hEQ : E ≤ Q (family P) a := inf_le_left.trans ((source_Z_Q_U h a).1.trans (map_subtype_le _))
  have hab := source_critical_one_adjacent hc hb
  have hDQ : D ≤ Q₀ := source_rankOne_pair_core_le_beta h hB d hab hbc hac Mb
  have hDC : D ≤ C₀ := le_inf hDQ
    ((le_centralizer_iff.mp (source_pair_core_normalizers h hab hbc).1).trans
      (centralizer_le (zpowers_le.mpr hy)))
  have hI : I = E ⊔ D := source_pair_adjacent_core_intersection h hB d hc hb hbc hac Mb
  have hkerB : π.ker ≤ B₀ := by
    intro x hx
    rw [hker] at hx
    exact (hI.le.trans (sup_le le_sup_left (hDC.trans le_sup_right))) hx
  have hn : C₀ ≤ normalizer (E : Set G) := inf_le_left.trans
    ((le_inf (source_adjacent_core_normalizes_center h hab) Q₀.le_normalizer).trans
      inf_normalizer_le_normalizer_inf)
  have hAB : A₀ ⊓ B₀ ≤ π.ker := by
    intro x hx
    have hxprod : x.val ∈ (E : Set G) * (C₀ : Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left E C₀ hn]
      exact hx.2
    obtain ⟨e,he,z,hz,hxz⟩ := hxprod
    have hzV : z ∈ V := by
      have hh := V.mul_mem (V.inv_mem (mem_sup_left he)) (mem_sup_right hx.1)
      change e⁻¹*x.val ∈ V at hh
      rw [←hxz] at hh
      simpa only [inv_mul_cancel_left] using hh
    have hzJ := hint.le ⟨hzV,hz.2⟩
    have hxQa : x.val ∈ Q (family P) a := by
      rw [←hxz]
      exact (Q (family P) a).mul_mem (hEQ he) (((source_Z_Q_U h a).1.trans (map_subtype_le _)) hzJ.1)
    rw [hker]
    exact ⟨hxQa,x.property⟩
  have hd : Disjoint (A₀.map π) (B₀.map π) := by
    apply disjoint_def.mpr
    rintro x ⟨v,hv,rfl⟩ ⟨z,hz,he⟩
    have hvz : v*z⁻¹ ∈ π.ker := by
      change π (v*z⁻¹) = 1
      rw [map_mul,map_inv,he,mul_inv_cancel]
    have hvB : v ∈ B₀ := by
      have hh := B₀.mul_mem (hkerB hvz) hz
      simpa only [inv_mul_cancel_right] using hh
    exact hAB ⟨hv,hvB⟩
  have hEmap : (E.subgroupOf Q₀).map π = ⊥ := by
    apply (Subgroup.map_eq_bot_iff _).mpr
    rw [hker]
    exact comap_mono (le_inf hEQ inf_le_right)
  have hBmap : B₀.map π = (C₀.subgroupOf Q₀).map π := by
    dsimp only [B₀]
    rw [subgroupOf_sup (show E ≤ Q₀ from inf_le_right) (show C₀ ≤ Q₀ from inf_le_left),
      Subgroup.map_sup,hEmap,bot_sup_eq]
  rw [hBmap] at hd
  have hcomm : A₀.map π ≤ centralizer ((C₀.subgroupOf Q₀).map π : Set K) := by
    rintro x ⟨v,hv,rfl⟩ z ⟨w,hw,rfl⟩
    have hcD : ⁅(w:G),(v:G)⁆ ∈ D :=
      source_rankOne_pair_core_action h hB d hc hb hbc Ma Mb
        (commutator_mem_commutator w.property (mem_sup_right hv))
    have hcπ : π ⁅w,v⁆ = 1 := by
      change ⁅w,v⁆ ∈ π.ker
      rw [hker]
      exact ⟨hcD.1,(⁅w,v⁆ : Q₀).property⟩
    have hc' : ⁅π w,π v⁆ = 1 := by
      rw [←map_commutatorElement]
      exact hcπ
    exact commutatorElement_eq_one_iff_mul_comm.mp hc'
  have hjoin : F ⊔ (E ⊔ C₀) = Q₀ := by
    rw [←sup_assoc,sup_comm F E]
    exact hsplit.symm
  have hgen : A₀.map π ⊔ (C₀.subgroupOf Q₀).map π = ⊤ := by
    rw [←hBmap,←Subgroup.map_sup,←subgroupOf_sup (show F ≤ Q₀ from inf_le_right)
      (show E ⊔ C₀ ≤ Q₀ from sup_le inf_le_right inf_le_left),hjoin,
      subgroupOf_self,map_top_of_surjective π hπ]
  let := source_center_elementary h c
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.of_le inf_le_left
  let : IsElementaryAbelian 2 A₀ := IsElementaryAbelian.subgroupOf inf_le_right
  let : IsElementaryAbelian 2 (A₀.map π) := IsElementaryAbelian.map π
  obtain ⟨e,he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting _ _ hd hcomm
  refine ⟨inferInstance,hd,e.trans ((MulEquiv.subgroupCongr hgen).trans topEquiv),?_⟩
  exact he


/-- DGS (11.3)(h) on the source Cartan-fixed triple. The exact further
quotient has no complementary two-group, since all its involutions lie in
its opposite-seed direct factor. -/
theorem source_rankOne_pair_core_span_of_supplement
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (hcover : (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2 ⊔
      ((stabilizer (family P) a ⊓ stabilizer (family P) b) ⊓ stabilizer (family P) c) =
        stabilizer (family P) a ⊓ stabilizer (family P) b) :
    Q (family P) b = pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b) ⊔
      (Q (family P) a ⊓ Q (family P) b) := by
  let := finite_endpoints h
  let Q₀ := Q (family P) b
  let I := Q (family P) a ⊓ Q₀
  let V := pairSpan (Z (family P) a) (Z (family P) c) Q₀
  let F := Z (family P) c ⊓ Q₀
  let : Finite Q₀ := Finite.of_injective (inclusion (Q_le_stabilizer _ b)) (inclusion_injective _)
  let hN : (I.subgroupOf Q₀).Normal := normal_subgroupOf_of_le_normalizer
    ((le_inf (source_adjacent_core_normalizes_core h (source_critical_one_adjacent hc hb).symm)
      Q₀.le_normalizer).trans inf_normalizer_le_normalizer_inf)
  let K := Q₀ ⧸ I.subgroupOf Q₀
  let π := QuotientGroup.mk' (I.subgroupOf Q₀)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  let : Finite K := Finite.of_surjective π hπ
  obtain ⟨y,hy,_,_,hgen,hint⟩ := source_rankOne_pair_coprime_splitting h hB d hc hb hbc hac Ma Mb
  let C₀ := Q₀ ⊓ centralizer (zpowers y : Set G)
  let A := (F.subgroupOf Q₀).map π
  let C := (C₀.subgroupOf Q₀).map π
  obtain ⟨_,hd,e,he⟩ := source_pair_further_split_images h hB d hc hb hbc hac Ma Mb
    π (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) y hy hgen hint
  change Disjoint A C at hd
  change A × C ≃* K at e
  have hΩ : omegaOneAmbient (⊤ : Subgroup K) = A := by
    have hh := source_opposite_seed_omega_image_of_supplement h hB d hc hb hbc hac Ma Mb hcover
      π (QuotientGroup.ker_mk' _)
    rwa [MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)] at hh
  have hC : C = ⊥ := by
    by_contra hn
    have hpK : IsPGroup 2 K := (isPGroup_pCoreIn 2 (stabilizer (family P) b)).of_surjective
      π hπ
    have hpC : IsPGroup 2 C := hpK.to_subgroup C
    have hcard : Nat.card C ≠ 1 := fun hh => hn (Subgroup.card_eq_one.mp hh)
    obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' 2 (hpC.card_eq_or_dvd.resolve_left hcard)
    have hx2 : (x:K)^2 = 1 := congrArg Subtype.val (hx ▸ pow_orderOf_eq_one x)
    have hxA : (x:K) ∈ A := by
      rw [←hΩ]
      exact (omegaOneAmbient_le_iff (⊤ : Subgroup K) _).mp le_rfl x (mem_top _) hx2
    have hx1 : x=1 := Subtype.ext (disjoint_def.mp hd hxA x.property)
    rw [hx1,orderOf_one] at hx
    omega
  have hA : A = ⊤ := by
    apply eq_top_iff.mpr
    intro x _
    obtain ⟨⟨v,z⟩,rfl⟩ := e.surjective x
    have hz : z=1 := Subtype.ext (hC.le z.property)
    rw [he,hz]
    simpa only [Subgroup.coe_one,mul_one] using v.property
  apply le_antisymm
  · intro x hx
    have hxA : π ⟨x,hx⟩ ∈ A := by rw [hA]; trivial
    obtain ⟨f,hf,hef⟩ := hxA
    have hk : f⁻¹ * ⟨x,hx⟩ ∈ π.ker := by
      change π (f⁻¹ * ⟨x,hx⟩) = 1
      rw [map_mul,map_inv,hef,inv_mul_cancel]
    rw [QuotientGroup.ker_mk'] at hk
    have hh := (V ⊔ I).mul_mem (mem_sup_left (mem_sup_right hf)) (mem_sup_right hk)
    change (f:G)*((f:G)⁻¹*x) ∈ V ⊔ I at hh
    simpa only [mul_inv_cancel_left] using hh
  · exact sup_le (pairSpan_le_core _ _ _) inf_le_right

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
