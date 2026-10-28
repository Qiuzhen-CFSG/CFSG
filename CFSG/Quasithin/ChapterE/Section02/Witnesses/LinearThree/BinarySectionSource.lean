module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.LinearThree.Original
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.BenderPlacement.SmallSectionBounds
public import Theory.GroupTheory.PResidual.NormalComplement
public import Theory.GroupTheory.PResidual.NormalSylowCommutator
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.CoreQuotient
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# Nonsolvable binary E.2.17 section producer

For the binary PSL₃(2) source row, the order-two star image has a genuine
lifted dihedral witness.  Its odd residual image forces the marked quaternion
core into the ambient two-core.  The resulting central section has the source
normality, centralization, elementary quotient, displacement, and full-residual
movement identities needed by the E.2.17 nonsolvable endpoint.

Source: Aschbacher–Smith, E.2.17, printed pp. 229–230.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Witnesses
open BenderPlacement
variable {H D : Type*} [Group H] [Finite H] [Group D] [Finite D]

theorem Involution.exists_original_with_odd_star_residual
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (V : Subgroup H) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hvn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hVM : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hcard : Nat.card (V.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) = 2) :
    ∃ w : OriginalWitness T (ChapterB.minimalParabolicMax T hP) V 1,
      Odd (Nat.card ((pResidual 2 w.pair.subgroup).map
        ((QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP)).comp w.pair.subgroup.subtype))) := by
  let J := ChapterB.minimalParabolicCore T hP
  let M := ChapterB.minimalParabolicMax T hP
  let q := QuotientGroup.mk' J
  let S := T.mapSurjective (QuotientGroup.mk'_surjective J)
  let W := V.map q
  let B := M.map q
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map q
  have hq := QuotientGroup.mk'_surjective J
  have hPs := ChapterB.minimalParabolic_surjective_core T hP q hq (by rw [QuotientGroup.ker_mk'])
  have hJs : ChapterB.minimalParabolicCore S hPs = ⊥ := by
    rw [←ChapterB.minimalParabolicCore_map_core T hP q hq (by rw [QuotientGroup.ker_mk'])]
    exact QuotientGroup.map_mk'_self J
  have hQs : pCore 2 (H ⧸ J) = ⊥ :=
    bot_unique (hJs ▸ ChapterB.minimalParabolicTwoCore_le_core S hPs)
  have hWM : W ≤ B.pCoreIn 2 := (map_mono hVM).trans (by
    have hh : (pCore 2 M).map (q.subgroupMap M) ≤ pCore 2 B :=
      le_sSup ⟨Normal.map inferInstance _ (q.subgroupMap_surjective M),pCore_isPGroup.map _⟩
    change ((pCore 2 M).map M.subtype).map q ≤ (pCore 2 B).map B.subtype
    have hh' := map_mono (f := B.subtype) hh
    rw [map_map, show B.subtype.comp (q.subgroupMap M) = q.comp M.subtype from rfl] at hh'
    simpa only [map_map] using hh')
  have hWS : W ≤ (S : Subgroup (H ⧸ J)) := map_mono hVT
  have hout : ¬ W ≤ pCore 2 (H ⧸ J) := by
    intro h
    have he : W = ⊥ := bot_unique (hQs ▸ h)
    have hc : Nat.card W = 1 := Subgroup.card_eq_one.mpr he
    change Nat.card W = 2 at hcard
    omega
  obtain ⟨p,hp,hp2,w,a,ha,⟨e⟩,hmax⟩ := Involution.exists_pair_of_card_two S B W hWS hWM hcard hout
  have hSM : (S : Subgroup (H ⧸ J)) ≤ B := map_mono (ChapterB.minimalParabolicMax_spec T hP).2
  have hsw : (w.sylow : Subgroup w.subgroup) = W.subgroupOf w.subgroup := by
    apply le_antisymm
    · intro x hx
      have hh : (x : H ⧸ J) ∈ B := hSM ((w.sylow_eq.le (mem_map_of_mem w.subgroup.subtype hx)).1)
      exact hmax.le hh
    · intro x hx
      have hh : (x : H ⧸ J) ∈ (w.sylow : Subgroup w.subgroup).map w.subgroup.subtype :=
        w.sylow_eq.ge ⟨hWS hx,x.property⟩
      obtain ⟨y,hy,he⟩ := hh
      exact w.subgroup.subtype_injective he ▸ hy
  have hswcard : Nat.card w.sylow = 2 := by
    rw [hsw,Nat.card_congr (subgroupOfEquivOfLe w.le).toEquiv]
    exact hcard
  have hodd := w.sylow.odd_card_twoResidual_of_isCyclic (isCyclic_of_prime_card hswcard)
  obtain ⟨w',r,hr,hrq,ξ,hξ⟩ := QuotientLift.lift_pair T hP V hVT hvn hVM w
  let wo : OriginalWitness T M V 1 :=
    ⟨w',1,by decide,one_dvd _,.dihedral rfl p a hp hp2 ha (ξ.trans e)⟩
  refine ⟨wo,?_⟩
  have heq : q.comp w'.subgroup.subtype = w.subgroup.subtype.comp r := by
    ext x
    exact (hrq x).symm
  change Odd (Nat.card ((pResidual 2 w'.subgroup).map (q.comp w'.subgroup.subtype)))
  rw [heq,←map_map,map_pResidual_of_surjective 2 r hr,
    card_map_of_injective w.subgroup.subtype_injective]
  exact hodd

theorem BenderPlacement.OriginalWitness.small_core_placement_of_odd_star_residual
    {T : Sylow 2 H} (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    {V U : Subgroup H} [IsElementaryAbelian 2 V] {n : ℕ}
    (w : OriginalWitness T (ChapterB.minimalParabolicMax T hP) V n)
    (hVT : V ≤ (T : Subgroup H))
    (hTV : (T : Subgroup H) ≤ normalizer (V : Set H))
    (hcore : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hout : ¬ V ≤ ChapterB.minimalParabolicCore T hP)
    (hfit : generalizedFitting H = pCore 2 H) (hV : Nat.card V = 16)
    (hTU : (T : Subgroup H) ≤ U) (hU : U ≤ normalizer (V : Set H))
    (f : U →* D) (hf : Function.Surjective f)
    (hk : f.ker = (centralizer (V : Set H)).subgroupOf U)
    (hD : Nat.card D ≤ 4)
    (hratio : 1 < cubicRatio (DihedralCubic.representation U V hU f hf hk))
    (hodd : Odd (Nat.card ((pResidual 2 w.pair.subgroup).map
      ((QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP)).comp w.pair.subgroup.subtype)))) :
    w.pair.subgroup.pCoreIn 2 ≤ pCore 2 H ∧
      w.pair.subgroup.pCoreIn 2 ⊓ V = pCore 2 H ⊓ V := by
  let J := ChapterB.minimalParabolicCore T hP
  let q := QuotientGroup.mk' J
  let P := w.pair.subgroup.pCoreIn 2
  let R := (pResidual 2 w.pair.subgroup).map (q.comp w.pair.subgroup.subtype)
  have hn := ChapterE.minimalParabolic_normalizer_le T hP V
    (IsElementaryAbelian.isPGroup 2 V) hTV hout
  have hPR := w.small_core_le_residual hVT hTV hcore hn hfit hV hTU hU f hf hk hD hratio
  have hmap : P.map q ≤ R := by
    change ((pCore 2 w.pair.subgroup).map w.pair.subgroup.subtype).map q ≤ _
    rw [map_map]
    exact map_mono hPR
  have h2 : IsPGroup 2 (P.map q) := (pCore_isPGroup.map w.pair.subgroup.subtype).map q
  have hbot : P.map q = ⊥ := by
    apply (P.map q).eq_bot_iff_forall.mpr
    intro x hx
    obtain ⟨m,hm⟩ := h2.exists_orderOf_eq_pow ⟨x,hx⟩
    have hord : orderOf x = 2^m := (Subgroup.orderOf_coe ⟨x,hx⟩).trans hm
    have hd : orderOf x ∣ Nat.card R := R.orderOf_dvd_natCard (hmap hx)
    have hc : Nat.Coprime (2^m) (Nat.card R) :=
      (Nat.coprime_two_left.mpr hodd).pow_left m
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hc (hord ▸ dvd_refl _) hd)
  have hPJ : P ≤ J := by
    simpa only [q,QuotientGroup.ker_mk'] using (map_eq_bot_iff P).mp hbot
  have hPT : P ≤ T := by
    change (pCore 2 w.pair.subgroup).map w.pair.subgroup.subtype ≤ _
    exact ((map_mono (pCore_isPGroup.le_sylow_of_normal w.pair.sylow)).trans_eq w.pair.sylow_eq).trans inf_le_left
  have hPQ : P ≤ pCore 2 H :=
    (le_inf hPT hPJ).trans_eq (ChapterB.minimalParabolic_sylow_inf_core T hP)
  refine ⟨hPQ,le_antisymm (inf_le_inf_right V hPQ) ?_⟩
  have hQ : (pCore 2 H).subgroupOf w.pair.subgroup ≤ pCore 2 w.pair.subgroup :=
    le_sSup ⟨inferInstance,pCore_isPGroup.comap_subtype⟩
  intro x hx
  exact ⟨mem_map_of_mem w.pair.subgroup.subtype (hQ (show
    (⟨x,w.pair.le hx.2⟩ : w.pair.subgroup) ∈ (pCore 2 H).subgroupOf w.pair.subgroup from hx.1)),hx.2⟩

theorem LinearThree.source_binary_image_card_two
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hm : ClassicalGroup.IsPSL
      (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 3 2)
    (V : Subgroup H) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hvn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hout : ¬ V ≤ ChapterB.minimalParabolicCore T hP) :
    Nat.card (V.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) = 2 := by
  let J := ChapterB.minimalParabolicCore T hP
  let q := QuotientGroup.mk' J
  let S := T.mapSurjective (QuotientGroup.mk'_surjective J)
  let W := V.map q
  let C := K.map q
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map q
  have hi := Structure.source_normal_simple_image T hP hs K hK hgen
  have hmin : ChapterB.IsMinimalParabolicOver S ⊤ :=
    (Structure.source_star_minimal_core_free T hP).1
  have hcore : ChapterB.minimalParabolicCore S hmin = ⊥ :=
    (Structure.source_star_minimal_core_free T hP).2
  have hWS : W ≤ (S : Subgroup (H ⧸ J)) := map_mono hVT
  have hSW : (S : Subgroup (H ⧸ J)) ≤ normalizer (W : Set (H ⧸ J)) :=
    (map_mono ((normal_subgroupOf_iff_le_normalizer hVT).mp hvn)).trans (le_normalizer_map q)
  have hne : W ≠ ⊥ := by
    intro hh
    have hle := (map_eq_bot_iff V).mp hh
    exact hout (by simpa only [q,QuotientGroup.ker_mk'] using hle)
  have hlt : ¬ 4 ≤ Nat.card W := by
    intro hc
    obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hm
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1)
      (by simpa only [Nat.card_eq_fintype_card,pow_one] using hcard)
    let : C.Normal := hi.2.2.1
    let : IsSimpleGroup C := hi.1
    have hcore' : (ChapterB.minimalParabolicMax S hmin).normalCore = ⊥ := by
      convert hcore using 1
      rfl
    have hh := LinearThree.one_lt_parameter F (n := 1) (by simpa using hcard) C e S
      (by decide) hi.2.2.2 hmin hcore' W hWS hSW hc
    omega
  change Nat.card W = 2
  have hpos := (one_lt_card_iff_ne_bot W).mpr hne
  obtain ⟨r,hr⟩ := (IsElementaryAbelian.isPGroup 2 W).exists_card_eq
  have hrlt : r < 2 := by
    by_contra! hh
    have := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hh
    norm_num at this
    omega
  interval_cases r
  · have hh : Nat.card W = 1 := by simpa using hr
    omega
  · simpa using hr

theorem BenderPlacement.OriginalWitness.small_core_fully_moved
    {T : Sylow 2 H} {N V U : Subgroup H} [IsElementaryAbelian 2 V] {n : ℕ}
    (w : OriginalWitness T N V n)
    (hVT : V ≤ (T : Subgroup H))
    (hTV : (T : Subgroup H) ≤ normalizer (V : Set H))
    (hcore : V ≤ N.pCoreIn 2) (hn : normalizer (V : Set H) ≤ N)
    (hfit : generalizedFitting H = pCore 2 H) (hV : Nat.card V = 16)
    (hTU : (T : Subgroup H) ≤ U) (hU : U ≤ normalizer (V : Set H))
    (f : U →* D) (hf : Function.Surjective f)
    (hk : f.ker = (centralizer (V : Set H)).subgroupOf U)
    (hD : Nat.card D ≤ 4)
    (hratio : 1 < cubicRatio (DihedralCubic.representation U V hU f hf hk)) :
    let P := w.pair.subgroup.pCoreIn 2
    let L := conjugateSpanBy (P ⊓ V) ⊤
    ⁅L,pResidual 2 H⁆ = L := by
  have hsmall := w.small_quaternion_core hVT hTV hcore hn hfit hV hTU hU f hf hk hD hratio
  obtain ⟨e⟩ := hsmall.2.2.2.1
  have hcard : Nat.card (w.pair.subgroup ⧸ pCore 2 w.pair.subgroup) = 6 := by
    rw [Nat.card_congr e.toEquiv,DihedralGroup.nat_card]
  let S := Classical.choice (inferInstance : Nonempty (Sylow 2 (w.pair.subgroup ⧸ pCore 2 w.pair.subgroup)))
  have hdiv : Nat.card S ∣ 2 := by
    obtain ⟨m,hm⟩ := S.isPGroup'.exists_card_eq
    have hd := (S : Subgroup (w.pair.subgroup ⧸ pCore 2 w.pair.subgroup)).card_subgroup_dvd_card
    rw [hcard] at hd
    have hc : Nat.Coprime (Nat.card S) 3 := by
      rw [hm]
      exact (by decide : Nat.Coprime 2 3).pow_left m
    exact hc.dvd_of_dvd_mul_right hd
  have hodd : Nat.Coprime 2 (Nat.card (pResidual 2 (w.pair.subgroup ⧸ pCore 2 w.pair.subgroup))) :=
    Nat.coprime_two_left.mpr (S.odd_card_twoResidual_of_isCyclic (isCyclic_of_card_dvd_prime hdiv))
  have hPR := w.small_core_le_residual hVT hTV hcore hn hfit hV hTU hU f hf hk hD hratio
  have hcomm : pCore 2 w.pair.subgroup = ⁅pCore 2 w.pair.subgroup,pResidual 2 w.pair.subgroup⁆ := by
    simpa only [inf_eq_left.mpr hPR] using core_inf_residual_eq_commutator_of_quotient_coprime hodd
  have hPL := w.small_core_le_span hVT hTV hcore hn hfit hV hTU hU f hf hk hD hratio
  let P := w.pair.subgroup.pCoreIn 2
  let L := conjugateSpanBy (P ⊓ V) ⊤
  let : L.Normal := normalizer_eq_top_iff.mp (top_unique (le_normalizer_conjugateSpanBy _ _))
  have hPm : P ≤ ⁅L,pResidual 2 H⁆ := by
    change (pCore 2 w.pair.subgroup).map w.pair.subgroup.subtype ≤ _
    have he := congrArg (map w.pair.subgroup.subtype) hcomm
    rw [map_commutator] at he
    exact he.le.trans (commutator_mono hPL (map_pResidual_le 2 w.pair.subgroup.subtype))
  exact le_antisymm (commutator_le_left _ _) (conjugateSpanBy_le (inf_le_left.trans hPm) le_normalizer_of_normal)

omit [Finite H] in
private theorem commutator_sup_right_le
    {R A B C : Subgroup H} [C.Normal]
    (hRA : ⁅R,A⁆ ≤ C) (hRB : ⁅R,B⁆ ≤ C) :
    ⁅R,A ⊔ B⁆ ≤ C := by
  let q := QuotientGroup.mk' C
  have hRA_map : ⁅R.map q,A.map q⁆ = ⊥ := by
    rw [← Subgroup.map_commutator]
    apply (Subgroup.map_eq_bot_iff (f := q) (H := ⁅R,A⁆)).2
    simpa [q] using hRA
  have hRB_map : ⁅R.map q,B.map q⁆ = ⊥ := by
    rw [← Subgroup.map_commutator]
    apply (Subgroup.map_eq_bot_iff (f := q) (H := ⁅R,B⁆)).2
    simpa [q] using hRB
  have hRA_cent : R.map q ≤ Subgroup.centralizer (A.map q : Set (H ⧸ C)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hRA_map
  have hRB_cent : R.map q ≤ Subgroup.centralizer (B.map q : Set (H ⧸ C)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hRB_map
  have hR_sup_cent :
      R.map q ≤ Subgroup.centralizer ((A.map q ⊔ B.map q : Subgroup (H ⧸ C)) : Set (H ⧸ C)) := by
    exact Subgroup.le_centralizer_sup_of_le_centralizers hRA_cent hRB_cent
  have hmap_bot : (⁅R,A ⊔ B⁆).map q = ⊥ := by
    rw [Subgroup.map_commutator, Subgroup.map_sup]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hR_sup_cent
  have hle_ker : ⁅R,A ⊔ B⁆ ≤ q.ker :=
    (Subgroup.map_eq_bot_iff (f := q) (H := ⁅R,A ⊔ B⁆)).mp hmap_bot
  simpa [q] using hle_ker

theorem source_core_centralizes_seed_section
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (V B Z : Subgroup H) [Z.Normal] (hBV : B ≤ V)
    (hres : (pResidual 2 (ChapterB.minimalParabolicMax T hP)).map
      (ChapterB.minimalParabolicMax T hP).subtype ≤ centralizer (V : Set H))
    (hQ : ⁅conjugateSpanBy B ⊤,pCore 2 H⁆ ≤ Z) :
    ⁅conjugateSpanBy B ⊤,ChapterB.minimalParabolicCore T hP⁆ ≤ Z := by
  let J := ChapterB.minimalParabolicCore T hP
  let R := (pResidual 2 J).map J.subtype
  have hR : R.Normal := ConjAct.normal_of_characteristic_of_normal
  let := hR
  have hRV : R ≤ centralizer (V : Set H) := by
    change (pResidual 2 ((ChapterB.minimalParabolicMax T hP).normalCore)).map
      (ChapterB.minimalParabolicMax T hP).normalCore.subtype ≤ centralizer (V : Set H)
    exact (embedded_pResidual_mono 2 (normalCore_le (ChapterB.minimalParabolicMax T hP))).trans hres
  have hRL : R ≤ centralizer (conjugateSpanBy B ⊤ : Set H) :=
    le_centralizer_conjugateSpanBy_of_normalizes R B ⊤ le_normalizer_of_normal
      (hRV.trans (centralizer_le hBV))
  obtain ⟨S,hS⟩ := ChapterB.minimalParabolic_twoCore_sylow_core T hP
  have he := congrArg (map J.subtype) (pResidual_sup_sylow_eq_top S)
  rw [Subgroup.map_sup,hS,map_subgroupOf_eq_of_le
    (ChapterB.minimalParabolicTwoCore_le_core T hP),←MonoidHom.range_eq_map,range_subtype] at he
  change ⁅conjugateSpanBy B ⊤,J⁆ ≤ Z
  rw [←he]
  apply commutator_sup_right_le
  · exact (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hRL)).le.trans bot_le
  · exact hQ

theorem LinearThree.source_binary_small_section
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hm : ClassicalGroup.IsPSL
      (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 3 2)
    (V : Subgroup H) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hvn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hcore : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hout : ¬ V ≤ ChapterB.minimalParabolicCore T hP)
    (hfit : generalizedFitting H = pCore 2 H) (hV : Nat.card V = 16)
    (U : Subgroup H) (hTU : (T : Subgroup H) ≤ U) (hU : U ≤ normalizer (V : Set H))
    (f : U →* D) (hf : Function.Surjective f)
    (hk : f.ker = (centralizer (V : Set H)).subgroupOf U)
    (hD : Nat.card D ≤ 4)
    (hratio : 1 < cubicRatio (DihedralCubic.representation U V hU f hf hk))
    (hres : (pResidual 2 (ChapterB.minimalParabolicMax T hP)).map
      (ChapterB.minimalParabolicMax T hP).subtype ≤ centralizer (V : Set H)) :
    ∃ w : OriginalWitness T (ChapterB.minimalParabolicMax T hP) V 1,
      let P := w.pair.subgroup.pCoreIn 2
      let Z := (center P).map P.subtype
      let B := P ⊓ V
      let L := conjugateSpanBy B ⊤
      P ≤ pCore 2 H ∧ B = pCore 2 H ⊓ V ∧
      Nonempty (QuaternionCentralProductData P) ∧
      ∃ hZn : Z.Normal, letI := hZn
        Z ≤ center H ∧ Z ≤ P ∧ P ≤ L ∧
        ⁅L,pCore 2 H⁆ ≤ Z ∧ ⁅L,ChapterB.minimalParabolicCore T hP⁆ ≤ Z ∧
        IsElementaryAbelian 2 (L.map (QuotientGroup.mk' Z)) ∧
        ⁅L,V⁆ ≤ B ∧ Nat.card B = 8 ∧ Nat.card Z = 2 ∧ ⁅L,pResidual 2 H⁆ = L := by
  have hcard := source_binary_image_card_two T hP hs K hK hgen hm V hVT hvn hout
  obtain ⟨w,hodd⟩ := Involution.exists_original_with_odd_star_residual T hP V hVT hvn hcore hcard
  have hTV := (normal_subgroupOf_iff_le_normalizer hVT).mp hvn
  have hn := ChapterE.minimalParabolic_normalizer_le T hP V
    (IsElementaryAbelian.isPGroup 2 V) hTV hout
  have hp := w.small_core_placement_of_odd_star_residual hP hVT hTV hcore hout hfit hV
    hTU hU f hf hk hD hratio hodd
  have hc := w.small_quaternion_core hVT hTV hcore hn hfit hV hTU hU f hf hk hD hratio
  obtain ⟨d⟩ := hc.1
  let P := w.pair.subgroup.pCoreIn 2
  let Z := (center P).map P.subtype
  let B := P ⊓ V
  let L := conjugateSpanBy B ⊤
  have hMV : ChapterB.minimalParabolicMax T hP ≤ normalizer (V : Set H) := by
    let M := ChapterB.minimalParabolicMax T hP
    have hTM : (T : Subgroup H) ≤ M := (ChapterB.minimalParabolicMax_spec T hP).2
    have he := congrArg (Subgroup.map M.subtype) (pResidual_sup_sylow_eq_top (T.subtype hTM))
    rw [Subgroup.map_sup,Sylow.coe_subtype,map_subgroupOf_eq_of_le hTM,
      ←MonoidHom.range_eq_map,range_subtype] at he
    change M ≤ normalizer (V : Set H)
    rw [←he]
    exact sup_le (hres.trans (Subgroup.centralizer_le_normalizer _)) hTV
  have hZc : Z ≤ center H := w.pair.core_center_le_ambient_center hTV hfit hp.1 hc.2.2.1
    d.center_card (ChapterB.minimalParabolicMax_spec T hP).1 hMV w.model.card_ne_one
  have hZn : Z.Normal := normalizer_eq_top_iff.mp (top_unique (by
    rw [←centralizer_eq_top_iff_subset.mpr hZc]
    exact Subgroup.centralizer_le_normalizer (Z : Set H)))
  let := hZn
  let : IsExtraspecial 2 P := d.extraspecial
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.of_le (p := 2) inf_le_right
  have hPP : ⁅P,P⁆ ≤ Z := by
    rw [←map_subtype_commutator]
    exact map_mono (IsExtraspecial.commutator_eq_center (p := 2)).le
  have hQ : pCore 2 H ≤ P ⊔ centralizer (B : Set H) := by
    apply le_trans ((pCore_isPGroup.le_sylow_of_normal T).trans hTU)
    rw [hc.2.1]
    exact sup_le_sup_left (inf_le_right.trans (centralizer_le (show B ≤ V from inf_le_right))) P
  obtain ⟨hCQ,hE⟩ := conjugateSpan_central_section_of_centralizing_supplement
    (pCore 2 H) P B Z hp.1 inf_le_left hQ hPP
  have hPL := w.small_core_le_span hVT hTV hcore hn hfit hV hTU hU f hf hk hD hratio
  have hLQ : L ≤ pCore 2 H := conjugateSpanBy_le (inf_le_left.trans hp.1) le_normalizer_of_normal
  have hLV : ⁅L,V⁆ ≤ B := by
    rw [show B = pCore 2 H ⊓ V from hp.2]
    refine le_inf ((commutator_mono hLQ le_rfl).trans (commutator_le_left _ _)) ?_
    rw [commutator_comm]
    exact le_normalizer_iff_commutator_le_left.mp
      (hLQ.trans ((pCore_isPGroup.le_sylow_of_normal T).trans hTV))
  have hBcard := w.small_seed_card hVT hTV hcore hn hfit hV hTU hU f hf hk hD hratio
  have hZcard : Nat.card Z = 2 := by
    rw [card_map_of_injective P.subtype_injective]
    exact d.center_card
  exact ⟨w,hp.1,hp.2,⟨d⟩,hZn,hZc,map_subtype_le _,hPL,hCQ,source_core_centralizes_seed_section T hP V B Z inf_le_right hres hCQ,hE,hLV,hBcard,hZcard,
    w.small_core_fully_moved hVT hTV hcore hn hfit hV hTU hU f hf hk hD hratio⟩
end CFSG.Quasithin.ChapterE.Witnesses
