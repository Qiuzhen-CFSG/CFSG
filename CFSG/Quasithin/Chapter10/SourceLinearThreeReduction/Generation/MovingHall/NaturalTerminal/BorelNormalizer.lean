module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.BothBlocks
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.OvergroupSylow
public import Stellmacher.BaumannTwoOvergroupNormalizer
public import Theory.GroupTheory.ConjugateOrbitIndexTwoStabilizer
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.OppositeBorels
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.EvenFieldBorel
/-!
# The original axis Borel has the prescribed half-Sylow subgroup

Every two-subgroup containing the original Baumann group normalizes it,
so it lies in the original maximal local M. The index-two component
stabilizer then makes any proper two-extension an ambient Sylow. Source
uniqueness above the original component orbit forces a competing local
overgroup into M, contradicting its escaping comparison block.

The relative Borel calculation supplies stabilizer invariance for either
original axis. Its nontrivial two-core gives the SQTK normalizer. Applying
these results to the selected opposite Borel discharges the Sylow and
SQTK premises on the literal original Hall subgroup. Natural marking,
Hall placement and the containing-component recognition remain with the
moving-Hall assembly owner.

Source: Aschbacher–Smith 10.2.3(4), printed p.747, using 1.2.7 and 10.2.1.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.MovingHall
open Chapter3.Section02 ChapterB
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

include D
private theorem maximal_normalizer_index
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    (normalizer (L.subgroupOf D.maximalLocal : Set D.maximalLocal)).index = 2 := by
  let M := D.maximalLocal
  have hLM : L ≤ M := (le_componentOrbit L T).trans (localOrbit T L).le_normalizer
  have hTM : (T : Subgroup G) ≤ M := le_normalizer_componentOrbit L T
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal
  have hlocal : IsSQTK KnownSimple.IsKnownSimple M :=
    D.simpleQTKE.twoLocal_sqtk hu.normalizer_maximal.1
  have hQ : IsSQTK KnownSimple.IsKnownSimple (M ⧸ pCore 2 M) := by
    refine ⟨?_, hlocal.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hlocal.stronglyQuasithin p hp ho)
  have hnot : ¬ (L.subgroupOf M).Normal := fun ha =>
    hn (hTM.trans ((normal_subgroupOf_iff_le_normalizer hLM).mp ha))
  exact ((Chapter1.Section02.proposition_1_2_1_three_index_knownSimple hQ
    D.component_in_maximalLocal).resolve_left hnot).1

/-- An escaping local overgroup containing the original factor has the prescribed Sylow. -/
theorem Context.local_outside_overgroup_sylow
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    {X : Subgroup G} (hcore : pCore 2 X ≠ ⊥)
    (hLX : L ≤ X)
    (hRX : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ X)
    (hout : ¬ X ≤ D.maximalLocal) :
    Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (L : Set G)) X := by
  let R := (T : Subgroup G) ⊓ normalizer (L : Set G)
  have hRT : R ≤ (T : Subgroup G) := inf_le_left
  have hi : R.relIndex (T : Subgroup G) = 2 := by
    have he : R.subgroupOf (T : Subgroup G) =
        (normalizer (L : Set G)).subgroupOf (T : Subgroup G) := by
      ext x
      exact and_iff_right x.property
    change (R.subgroupOf (T : Subgroup G)).index = 2
    rw [he]
    exact source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 ctx.nonnormal
  apply Chapter1.isSylowIn_iff.mpr
  refine ⟨T.isPGroup'.to_le hRT, hRX, ?_⟩
  intro U hU hRU hUX
  by_contra hneU
  obtain ⟨Q, hUQ⟩ := hU.exists_le_sylow
  have hRQ : R ≤ (Q : Subgroup G) := hRU.trans hUQ
  have hindexQ : R.relIndex (Q : Subgroup G) = 2 := by
    have hcardQ := relIndex_mul_relIndex (⊥ : Subgroup G) R (Q : Subgroup G) bot_le hRQ
    have hcardT := relIndex_mul_relIndex (⊥ : Subgroup G) R (T : Subgroup G) bot_le hRT
    simp only [relIndex_bot_left] at hcardQ hcardT
    rw [hi] at hcardT
    have hQT : Nat.card Q = Nat.card T := Nat.card_congr (Q.equiv T).toEquiv
    exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := R))
      (hcardQ.trans (hQT.trans hcardT.symm))
  have hiU : R.relIndex U = 2 := by
    have hd : R.relIndex U ∣ 2 := hindexQ ▸
      dvd_of_mul_right_eq _ (relIndex_mul_relIndex R U (Q : Subgroup G) hRU hUQ)
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
    · exact (hneU (le_antisymm (relIndex_eq_one.mp h) hRU)).elim
    · exact h
  have hUQeq : U = (Q : Subgroup G) := by
    have hh := relIndex_mul_relIndex R U (Q : Subgroup G) hRU hUQ
    rw [hiU, hindexQ] at hh
    exact le_antisymm hUQ (relIndex_eq_one.mp (by omega : U.relIndex (Q : Subgroup G) = 1))
  have hSU : baumann (T : Subgroup G) ≤ U :=
    (le_inf inf_le_left (ctx.baumann_normalizes_original D n hn hF e)).trans hRU
  have hUM : U ≤ D.maximalLocal :=
    (twoSubgroup_le_normalizer_baumann T U hU hSU).trans
      (ctx.original_baumann_normalizer_le D n hn hF e)
  have hQM : (Q : Subgroup G) ≤ D.maximalLocal := hUQeq ▸ hUM
  have hUN : ¬ U ≤ normalizer (L : Set G) := by
    intro hUN
    have hLM : L ≤ D.maximalLocal :=
      (le_componentOrbit L T).trans (localOrbit T L).le_normalizer
    have hQN : ((Q.subtype hQM : Sylow 2 D.maximalLocal) : Subgroup D.maximalLocal) ≤
        normalizer (L.subgroupOf D.maximalLocal : Set D.maximalLocal) := by
      rw [← subgroupOf_normalizer_eq hLM]
      intro x hx
      exact hUN (hUQeq.symm ▸ hx)
    apply (Q.subtype hQM).not_dvd_index
    have hd := index_dvd_of_le hQN
    rwa [maximal_normalizer_index D ctx.nonnormal] at hd
  obtain ⟨x, hxU, hxN⟩ := SetLike.not_le_iff_exists.mp hUN
  obtain ⟨t, ht, htn, hpair, _⟩ := source_nonnormal_pair D.simpleQTKE D.maximal.1 ctx.nonnormal
  have hxconj : L.map (MulAut.conj x).toMonoidHom = L.map (MulAut.conj t).toMonoidHom :=
    (source_nonnormal_maximal_pair D ctx.nonnormal ht htn x (hUM hxU)).resolve_left
      (fun he => hxN (mem_normalizer_iff_map_conj_eq.mpr he))
  have hLtX : L.map (MulAut.conj t).toMonoidHom ≤ X := by
    rw [← hxconj]
    rintro _ ⟨l, hl, rfl⟩
    exact X.mul_mem (X.mul_mem (hUX hxU) (hLX hl)) (X.inv_mem (hUX hxU))
  have hOrbitX : localOrbit T L ≤ X := by
    rw [hpair]
    exact sup_le hLX hLtX
  obtain ⟨N, hN, hXN⟩ := exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot X hcore
  have hNM := source_overgroup_eq_of_maximal_sylow D Q hQM hN
    (hOrbitX.trans hXN) ((hUQeq ▸ hUX).trans hXN)
  exact hout (hNM ▸ hXN)


/-- The same conclusion holds for either original factor, keeping the original setup. -/
theorem Context.factor_outside_overgroup_sylow
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    {t : G} (ht : t ∈ (T : Subgroup G))
    {X : Subgroup G} (hcore : pCore 2 X ≠ ⊥)
    (hLX : L ≤ X ∨ L.map (MulAut.conj t).toMonoidHom ≤ X)
    (hRX : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ X)
    (hout : ¬ X ≤ D.maximalLocal) :
    Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (L : Set G)) X := by
  rcases hLX with hLX | hLX
  · exact ctx.local_outside_overgroup_sylow D n hn hF e hcore hLX hRX hout
  let f := MulAut.conj t
  let R := (T : Subgroup G) ⊓ normalizer (L : Set G)
  have hi := source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 ctx.nonnormal
  have hRT : (R.subgroupOf (T : Subgroup G)).Normal := by
    have he : R.subgroupOf (T : Subgroup G) = (normalizer (L : Set G)).subgroupOf (T : Subgroup G) := by
      ext x
      exact and_iff_right x.property
    rw [he]
    exact normal_of_index_eq_two hi
  have hTR : (T : Subgroup G) ≤ normalizer (R : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (show R ≤ (T : Subgroup G) from inf_le_left)).mp hRT
  have hRf : R.map f.toMonoidHom = R := mem_normalizer_iff_map_conj_eq.mp (hTR ht)
  have hMf : D.maximalLocal.map f.toMonoidHom = D.maximalLocal :=
    mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal.le_normalizer ((le_normalizer_componentOrbit L T) ht))
  have hLXX : L ≤ X.map f.toMonoidHom := by
    have hh := map_mono (f := f.toMonoidHom) hLX
    rwa [conjugate_twice_eq_of_index_two L (T : Subgroup G) (normalizer (L : Set G)) hi inf_le_right ht] at hh
  have hRXX : R ≤ X.map f.toMonoidHom := by
    have hh := map_mono (f := f.toMonoidHom) hRX
    rwa [hRf] at hh
  have hcXX : pCore 2 (X.map f.toMonoidHom) ≠ ⊥ := by
    intro he
    let a : X ≃* X.map f.toMonoidHom := f.subgroupMap X
    have hh : (pCore 2 X).map a.toMonoidHom = pCore 2 (X.map f.toMonoidHom) := pCore_map_iso 2 a
    rw [he] at hh
    exact hcore ((map_eq_bot_iff_of_injective _ a.injective).mp hh)
  have hoXX : ¬ X.map f.toMonoidHom ≤ D.maximalLocal := by
    intro he
    exact hout ((map_le_map_iff_of_injective f.injective).mp (he.trans_eq hMf.symm))
  have hp := ctx.local_outside_overgroup_sylow D n hn hF e hcXX hLXX hRXX hoXX
  apply (Chapter1.IsSylowIn.map_iff f.toMonoidHom f.injective).mp
  rwa [hRf]


omit D [Finite G] in
private theorem normalizer_core_ne_bot (A : Subgroup G) (hA : pCore 2 A ≠ ⊥) :
    pCore 2 (normalizer (A : Set G)) ≠ ⊥ := by
  have hQ : A.pCoreIn 2 ≠ ⊥ := fun he => hA
    ((map_eq_bot_iff_of_injective _ A.subtype_injective).mp he)
  have hle : A.pCoreIn 2 ≤ (normalizer (A : Set G)).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 A)
      ((pCoreIn_le 2 A).trans A.le_normalizer)
      (normalizer_le_normalizer_characteristic_image A (pCore 2 A))
  intro he
  apply hQ
  apply bot_unique
  exact hle.trans (by change (pCore 2 (normalizer (A : Set G))).map _ ≤ ⊥; simp [he])

/-- The actual axis Borel supplies its core, stabilizer invariance and local SQTK condition. -/
theorem Context.axis_borel_normalizer_sylow
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) (mark : NaturalMarking D e)
    (hBB : B.map H.subtype ≤ sourceOrbitBorel T L)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (A K : Subgroup G) (hAB : A ≤ B.map H.subtype)
    (hA : Nat.card A = 2 ^ n - 1)
    (hfactor : A ≤ L ∨ A ≤ L.map (MulAut.conj t).toMonoidHom)
    (hKN : K ≤ normalizer ((⁅baumann (T : Subgroup G),A⁆ ⊔ A : Subgroup G) : Set G))
    (hout : ¬ K ≤ D.maximalLocal) :
    Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (L : Set G))
      (normalizer ((⁅baumann (T : Subgroup G),A⁆ ⊔ A : Subgroup G) : Set G)) ∧
    IsSQTK KnownSimple.IsKnownSimple
      (normalizer ((⁅baumann (T : Subgroup G),A⁆ ⊔ A : Subgroup G) : Set G)) := by
  obtain ⟨E,J,hE,hJ,heq,hUJ,hBJ,hlocal,hv,hfixed,hgen,hcover,hcard,hcyclic,
    hBN,hBNt,hbL,hLn,hcore,hz,_⟩ :=
    ctx.component_with_both_block_geometry D n hn hF e mark hBB
  let S := baumann (T : Subgroup G)
  let R := (T : Subgroup G) ⊓ normalizer (L : Set G)
  let L₂ := L.map (MulAut.conj t).toMonoidHom
  let A₀ := (⁅S,A⁆ ⊔ A : Subgroup G)
  let N := normalizer (A₀ : Set G)
  have hne : A ≠ ⊥ := by
    intro he
    rw [he,card_bot] at hA
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ n by omega)
    norm_num at hp
    omega
  have hodd := ctx.odd_card_of_le_hall_image A hAB
  have hAS : A ≤ normalizer (S : Set G) :=
    hAB.trans (ctx.original_block_hall_normalizes_baumann D n hn hF e mark hBB hbL)
  have hRS : R ≤ normalizer (S : Set G) :=
    inf_le_left.trans ((T : Subgroup G).le_normalizer.trans (normalizer_le_normalizer_baumann _))
  have hcomm : L ≤ centralizer (L₂ : Set G) :=
    source_original_block_commutes_prescribed_conjugate D hbL ht htn
  have hg : pCore 2 A₀ ≠ ⊥ ∧ R ≤ N ∧ (L ≤ N ∨ L₂ ≤ N) := by
    rcases hfactor with hAL | hAL
    · obtain ⟨hS,hP,_,_⟩ := ctx.original_block_axis_borel D n hn hF e mark hBB hbL A hAL hAB hne
      have hPL : A₀ ≤ L := sup_le (by rw [hS]; exact inf_le_right) hAL
      refine ⟨hLn.2.1.borel_core_ne_bot L _ A hP (normalizer_commutator_ge_right S A),?_,?_⟩
      · change R ≤ normalizer ((⁅S,A⁆ ⊔ A : Subgroup G) : Set G)
        rw [hS]
        exact Chapter1.sl2_sylow_odd_borel_normalized L S A R e (hS ▸ hP) hAL
          (hA.trans (congrArg (fun q : ℕ => q-1) hF.symm)) hodd hAS inf_le_right hRS
      · exact Or.inr (((le_centralizer_iff.mp hcomm).trans (centralizer_le hPL)).trans
          (Subgroup.centralizer_le_normalizer _))
    · obtain ⟨hS,hP⟩ := ctx.original_conjugate_axis_sylow D n hn hF e mark hBB hbL ht A hAL hAB hne
      let a : L ≃* L₂ := (MulAut.conj t).subgroupMap L
      let e₂ := (QuotientGroup.congr _ _ a.symm (pCore_map_iso 2 a.symm)).trans e
      have hPL : A₀ ≤ L₂ := sup_le (by rw [hS]; exact inf_le_right) hAL
      have hRL : R ≤ normalizer (L₂ : Set G) :=
        index_two_stabilizer_normalizes_conjugate L (T : Subgroup G)
          (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 ctx.nonnormal) ht
      refine ⟨(hLn.2.1.of_mulEquiv a).borel_core_ne_bot L₂ _ A hP
        (normalizer_commutator_ge_right S A),?_,?_⟩
      · change R ≤ normalizer ((⁅S,A⁆ ⊔ A : Subgroup G) : Set G)
        rw [hS]
        exact Chapter1.sl2_sylow_odd_borel_normalized L₂ S A R e₂ (hS ▸ hP) hAL
          (hA.trans (congrArg (fun q : ℕ => q-1) hF.symm)) hodd hAS hRL hRS
      · exact Or.inl ((hcomm.trans (centralizer_le hPL)).trans (Subgroup.centralizer_le_normalizer _))
  exact ⟨ctx.factor_outside_overgroup_sylow D n hn hF e ht
    (normalizer_core_ne_bot A₀ hg.1) hg.2.2 hg.2.1 (fun hNM => hout (hKN.trans hNM)),
    source_natural_borel_normalizer_sqtk D A₀ hg.1⟩

/-- The selected opposite original Hall axis has the source half-Sylow normalizer. -/
theorem Context.exists_axis_borel_normalizer_sylow
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) (mark : NaturalMarking D e)
    (hBB : B.map H.subtype ≤ sourceOrbitBorel T L) :
    ∃ K : Subgroup H, ChapterC.IsBlock K ∧ ChapterC.IsL2EvenBlock K n ∧
      pCore 2 K = ChapterC.blockU K ∧ center K = ⊥ ∧ ¬ K.map H.subtype ≤ D.maximalLocal ∧
    ∃ (t : G) (_ht : t ∈ (T : Subgroup G)), t ∉ normalizer (L : Set G) ∧
    ∃ A : Subgroup G, A ≤ B.map H.subtype ∧
      (A ≤ L ∨ A ≤ L.map (MulAut.conj t).toMonoidHom) ∧ Nat.card A = 2^n-1 ∧
      K.map H.subtype ≤ centralizer ((⁅baumann (T : Subgroup G),A⁆ ⊔ A : Subgroup G) : Set G) ∧
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (L : Set G))
        (normalizer ((⁅baumann (T : Subgroup G),A⁆ ⊔ A : Subgroup G) : Set G)) ∧
      IsSQTK KnownSimple.IsKnownSimple
        (normalizer ((⁅baumann (T : Subgroup G),A⁆ ⊔ A : Subgroup G) : Set G)) := by
  obtain ⟨E,K,hE,hK,heq,hUK,hBK,hlocal,hv,hfixed,hgen,hcover,hcard,hcyclic,
    hBN,hBNt,hbL,hnatL,hcoreL,hzL,hborelL,hbK,hnatK,hcoreK,hzK,hSK,haxis,haxisS,
    t,ht,htn,a,hfirst,hsecond,hor,hA₁L,hA₂L,hcard₁,hcard₂,hdis,hjoin,hcy₁,hcy₂,hcommon,
    hop,hne,hcomm,hout⟩ := ctx.component_with_opposite_borel_geometry D n hn hF e mark hBB
  refine ⟨K,hbK,hnatK,hcoreK,hzK,hout,t,ht,htn,?_⟩
  rcases hop with ⟨_,hc⟩ | ⟨_,hc⟩
  · have hC := le_centralizer_iff.mp hc
    have hA : _ = 2^n-1 := hcard₂.trans (congrArg (fun q : ℕ => q-1) hF)
    exact ⟨_,map_subtype_le _,Or.inr hA₂L,hA,hC,
      ctx.axis_borel_normalizer_sylow D n hn hF e mark hBB ht htn _ _ (map_subtype_le _)
        hA (Or.inr hA₂L) (hC.trans (Subgroup.centralizer_le_normalizer _)) hout⟩
  · have hC := le_centralizer_iff.mp hc
    have hA : _ = 2^n-1 := hcard₁.trans (congrArg (fun q : ℕ => q-1) hF)
    exact ⟨_,map_subtype_le _,Or.inl hA₁L,hA,hC,
      ctx.axis_borel_normalizer_sylow D n hn hF e mark hBB ht htn _ _ (map_subtype_le _)
        hA (Or.inl hA₁L) (hC.trans (Subgroup.centralizer_le_normalizer _)) hout⟩

end CFSG.Quasithin.Chapter10.MovingHall
