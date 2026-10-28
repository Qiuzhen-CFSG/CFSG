module
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.LowerObstructions.PSL2.ElementaryLift
public import CFSG.Quasithin.ChapterE.Section01.Inheritance
public import Theory.GroupTheory.ConjugateSpanNormalClosure
public import Theory.GroupTheory.PResidual.PerfectImage
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PPerfectHom
public import Theory.GroupTheory.SubgroupConjugation
public import Theory.GroupTheory.SylowNormalRestriction

/-!
# E-generation obstructed by two exchanged rank-one factors

An elementary lift of a Sylow subgroup on each of two simple rank-one
factors supplies an invariant elementary family. Its weak closure has image
the Sylow intersection with their normal product. E.1.4 confines every
small-rank E-member: if it misses its actor's factor, its residual image
lies in the Sylow intersection and vanishes by two-perfectness; otherwise
that factor preserves the actor's rank through the literal solvable kernel.
Thus both the weak-closure normalizer and all such members lie in the same
proper normalizer. No generation-parameter descent through a quotient is used.

The application is the paired natural SL₂ row of E.2.3 in source 6.1.5.
Source: Aschbacher--Smith E.1.2--6 and E.2.3, pp.209--210,216--217.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.PairLift
variable {G Q : Type*} [Group G] [Finite G] [Group Q] [Finite Q]

omit [Finite Q] in
private theorem conjugateSpan_le_sylow_intersection
    (S : Sylow 2 Q) (Y : Subgroup Q)
    (L : Fin 2 → Subgroup Q) (P : ∀ i, Sylow 2 (L i))
    (hLY : ∀ i, L i ≤ Y)
    (hP : ∀ i, (P i : Subgroup (L i)).map (L i).subtype = (S : Subgroup Q) ⊓ L i)
    (hproper : ∀ i (D : Subgroup (L i)), (P i : Subgroup (L i)) ≤ D → D ≠ ⊤ →
      D ≤ normalizer (P i : Set (L i)))
    (hperm : ∀ g : Q, ∀ i, ∃ j, (L i).map (MulAut.conj g).toMonoidHom = L j)
    (K : Subgroup Q) (hBK : (S : Subgroup Q) ⊓ Y ≤ K)
    (i : Fin 2) (hnot : ¬ L i ≤ K) :
    conjugateSpanBy ((P i : Subgroup (L i)).map (L i).subtype) K ≤
      (S : Subgroup Q) ⊓ Y := by
  rw [conjugateSpanBy_eq_iSup_conj]
  apply iSup_le
  intro k
  obtain ⟨j,hj⟩ := hperm k i
  let R := ((P i : Subgroup (L i)).map (L i).subtype).map
    (MulAut.conj (k : Q)).toMonoidHom
  have hRK : R ≤ K := by
    rintro _ ⟨x,hx,rfl⟩
    rw [hP i] at hx
    exact K.mul_mem (K.mul_mem k.property (hBK ⟨hx.1,hLY i hx.2⟩)) (K.inv_mem k.property)
  have hRL : R ≤ L j := hj ▸ map_mono (map_subtype_le _)
  have hnotj : ¬ L j ≤ K := by
    intro h
    apply hnot
    intro x hx
    have hh : (k : Q) * x * (k : Q)⁻¹ ∈ K :=
      h (hj ▸ mem_map_of_mem (MulAut.conj (k : Q)).toMonoidHom hx)
    have hh' := K.mul_mem (K.mul_mem (K.inv_mem k.property) hh) k.property
    simpa only [mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one] using hh'
  have hPK : (P j : Subgroup (L j)) ≤ K.subgroupOf (L j) := by
    apply map_le_iff_le_comap.mp
    rw [hP j]
    exact (inf_le_inf_left _ (hLY j)).trans hBK
  have hn := hproper j (K.subgroupOf (L j)) hPK
    (fun he => hnotj (subgroupOf_eq_top.mp he))
  have hp : IsPGroup 2 (R.subgroupOf (L j)) :=
    (((P i).isPGroup'.map (L i).subtype).map (MulAut.conj (k : Q)).toMonoidHom).comap_subtype
  have hrn : R.subgroupOf (L j) ≤ normalizer (P j : Set (L j)) :=
    (comap_mono hRK).trans hn
  have hrp : R.subgroupOf (L j) ≤ (P j : Subgroup (L j)) := by
    have hh := hp.inf_normalizer_sylow (P j)
    rw [inf_eq_left.mpr hrn] at hh
    exact inf_eq_left.mp hh.symm
  have hr := map_mono (f := (L j).subtype) hrp
  rw [map_subgroupOf_eq_of_le hRL,hP j] at hr
  exact hr.trans (inf_le_inf_left _ (hLY j))

private theorem image_twoGroup_of_residual_image_le
    (q : G →* Q) (K : Subgroup G) (B : Subgroup Q) (hB : IsPGroup 2 B)
    (h : ((pResidual 2 K).map K.subtype).map q ≤ B) : IsPGroup 2 (K.map q) := by
  let f : pResidual 2 K →* B :=
    ((q.comp K.subtype).comp (pResidual 2 K).subtype).codRestrict B
      (fun x => h (mem_map_of_mem q (mem_map_of_mem K.subtype x.property)))
  have hf := (isPPerfect_pResidual (G := K) 2).hom_eq_one_of_isPGroup hB f
  have hm : ((pResidual 2 K).map K.subtype).map q = ⊥ := by
    apply bot_unique
    rintro _ ⟨x,⟨y,hy,rfl⟩,rfl⟩
    exact congrArg Subtype.val (DFunLike.congr_fun hf ⟨y,hy⟩)
  rw [map_embedded_pResidual] at hm
  have hz : pResidual 2 (K.map q) = ⊥ :=
    (map_eq_bot_iff_of_injective _ (K.map q).subtype_injective).mp hm
  exact (isPGroup_quotient_pResidual 2).of_equiv
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot)

private theorem twoGroup_overgroup_normalizes_intersection
    (S : Sylow 2 Q) (Y : Subgroup Q) [Y.Normal]
    (K : Subgroup Q) (hK : IsPGroup 2 K)
    (hBK : (S : Subgroup Q) ⊓ Y ≤ K) :
    K ≤ normalizer (((S : Subgroup Q) ⊓ Y : Subgroup Q) : Set Q) := by
  obtain ⟨P,hP⟩ := S.exists_sylow_map_eq_inf_of_normal Y
  have hPK : (P : Subgroup Y) ≤ K.subgroupOf Y :=
    map_le_iff_le_comap.mp (hP ▸ hBK)
  have he := P.is_maximal' hK.comap_subtype hPK
  have he' : (S : Subgroup Q) ⊓ Y = K ⊓ Y := by
    rw [←hP,←subgroupOf_map_subtype]
    exact congrArg (map Y.subtype) he.symm
  rw [he']
  exact (le_inf K.le_normalizer le_normalizer_of_normal).trans inf_normalizer_le_normalizer_inf

omit [Finite G] [Finite Q] in
private theorem sylow_intersection_le_map_tau
    (T : Sylow 2 G) (q : G →* Q) (A : Subgroup G)
    (hAT : A ≤ (T : Subgroup G))
    (hker : (T : Subgroup G) ⊓ q.ker = pCore 2 G)
    (B : Subgroup Q) (hBT : B ≤ (T : Subgroup G).map q)
    (hBC : B ≤ centralizer (A.map q : Set Q)) :
    B ≤ (tau (T : Subgroup G) A).map q := by
  intro b hb
  obtain ⟨t,ht,rfl⟩ := hBT hb
  refine ⟨t,mem_centralizerModulo_iff.mpr ⟨ht,?_⟩,rfl⟩
  intro a ha
  rw [←hker]
  refine ⟨?_,?_⟩
  · exact (T : Subgroup G).mul_mem ((T : Subgroup G).mul_mem
      ((T : Subgroup G).mul_mem (hAT ha) ht) ((T : Subgroup G).inv_mem (hAT ha)))
      ((T : Subgroup G).inv_mem ht)
  · change q ⁅a,t⁆ = 1
    rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm]
    exact hBC hb (q a) (mem_map_of_mem q ha)

private theorem member_le_normalizer_of_pair_lift
    (q : G →* Q) (hq : Function.Surjective q) (T : Sylow 2 G)
    (Y : Subgroup Q) [Y.Normal]
    (L : Fin 2 → Subgroup Q) (P : ∀ i, Sylow 2 (L i))
    (hLY : ∀ i, L i ≤ Y)
    (hP : ∀ i, (P i : Subgroup (L i)).map (L i).subtype =
      (T : Subgroup G).map q ⊓ L i)
    (hproper : ∀ i (D : Subgroup (L i)), (P i : Subgroup (L i)) ≤ D → D ≠ ⊤ →
      D ≤ normalizer (P i : Set (L i)))
    (hperm : ∀ g : Q, ∀ i, ∃ j, (L i).map (MulAut.conj g).toMonoidHom = L j)
    (hLs : ∀ i, IsSimpleGroup (L i)) (hLn : ∀ i, ¬ Group.IsSolvable (L i))
    (r : ℕ) (hr : ∀ i, r < Group.rank (P i))
    (A K : Subgroup G) (hK : IsEMemberAt r (T : Subgroup G) A K)
    (i : Fin 2) (hA : A.map q = (P i : Subgroup (L i)).map (L i).subtype)
    (htau : (T : Subgroup G).map q ⊓ Y ≤ (tau (T : Subgroup G) A).map q) :
    K ≤ (normalizer (((T : Subgroup G).map q ⊓ Y : Subgroup Q) : Set Q)).comap q := by
  let S := T.mapSurjective hq
  let B : Subgroup Q := (S : Subgroup Q) ⊓ Y
  let : IsSimpleGroup (L i) := hLs i
  have hAL : A.map q ≤ L i := hA ▸ map_subtype_le _
  by_cases hLK : L i ≤ K.map q
  · exfalso
    have hri : r < Group.rank (A.map q) := by
      rw [hA]
      exact (hr i).trans_eq (Group.rank_congr
        ((P i : Subgroup (L i)).equivMapOfInjective (L i).subtype (L i).subtype_injective))
    rcases hK.2 with ho | hc
    · let : Group.IsNilpotent (pCore 2 K) := pCore_isPGroup.isNilpotent
      exact (not_le_of_gt hri) ((Subgroup.RankOneSylowExtension.rank_image_le_solvable_quotient_image
        q (L i) (hLn i) A K hK.1.2.2.1 hAL hLK (pCore 2 K)).trans ho.2)
    · exact (not_le_of_gt hri) ((Subgroup.RankOneSylowExtension.rank_image_le_solvable_quotient_image
        q (L i) (hLn i) A K hK.1.2.2.1 hAL hLK (solvableRadical K)).trans hc.2)
  · have hBK : B ≤ K.map q := htau.trans (map_mono (hK.1.2.2.2.1.trans inf_le_right))
    have hspan := conjugateSpan_le_sylow_intersection S Y L P hLY hP hproper hperm
      (K.map q) hBK i hLK
    have hres : ((pResidual 2 K).map K.subtype).map q ≤ B := by
      have hh := map_mono (f := q.comp K.subtype) hK.1.residual_le_normalClosure
      rw [map_normalClosure_eq_conjugateSpanBy_range] at hh
      have hAi : (A.subgroupOf K).map (q.comp K.subtype) = A.map q := by
        rw [←map_map,map_subgroupOf_eq_of_le hK.1.2.2.1]
      have hrange : (q.comp K.subtype).range = K.map q := by
        rw [MonoidHom.range_comp,range_subtype]
      rw [hAi,hrange,hA] at hh
      have hh' : ((pResidual 2 K).map K.subtype).map q ≤
          conjugateSpanBy ((P i : Subgroup (L i)).map (L i).subtype) (K.map q) := by
        simpa only [map_map] using hh
      exact hh'.trans hspan
    have hp : IsPGroup 2 (K.map q) :=
      image_twoGroup_of_residual_image_le q K B (S.isPGroup'.to_le inf_le_left) hres
    exact map_le_iff_le_comap.mp
      (twoGroup_overgroup_normalizes_intersection S Y (K.map q) hp hBK)

theorem not_isEGenerated_of_pair_lifts
    (q : G →* Q) (hq : Function.Surjective q) (T : Sylow 2 G)
    (hker : (T : Subgroup G) ⊓ q.ker = pCore 2 G)
    (hcore : pCore 2 Q = ⊥)
    (Y : Subgroup Q) [Y.Normal]
    (L : Fin 2 → Subgroup Q) (P : ∀ i, Sylow 2 (L i))
    (hLY : ∀ i, L i ≤ Y)
    (hP : ∀ i, (P i : Subgroup (L i)).map (L i).subtype =
      (T : Subgroup G).map q ⊓ L i)
    (hspan : (T : Subgroup G).map q ⊓ Y =
      ⨆ i, (P i : Subgroup (L i)).map (L i).subtype)
    (hcomm : IsMulCommutative ((T : Subgroup G).map q ⊓ Y : Subgroup Q))
    (hproper : ∀ i (D : Subgroup (L i)), (P i : Subgroup (L i)) ≤ D → D ≠ ⊤ →
      D ≤ normalizer (P i : Set (L i)))
    (hperm : ∀ g : Q, ∀ i, ∃ j, (L i).map (MulAut.conj g).toMonoidHom = L j)
    (hLs : ∀ i, IsSimpleGroup (L i)) (hLn : ∀ i, ¬ Group.IsSolvable (L i))
    (hcard : ∀ i j, Nat.card (P i) = Nat.card (P j))
    (r : ℕ) (hr : ∀ i, r < Group.rank (P i))
    (hlift : ∀ i, ∃ A : Subgroup G, IsElementaryAbelian 2 A ∧
      A ≤ (T : Subgroup G) ∧ A.map q = (P i : Subgroup (L i)).map (L i).subtype) :
    ¬ IsEGenerated r G := by
  let S := T.mapSurjective hq
  let B : Subgroup Q := (S : Subgroup Q) ⊓ Y
  let E (i : Fin 2) : Subgroup Q := (P i : Subgroup (L i)).map (L i).subtype
  have hEB (i) : E i ≤ B := by
    change (P i : Subgroup (L i)).map (L i).subtype ≤ B
    rw [hP i]
    exact inf_le_inf_left _ (hLY i)
  have hcE (i) : Nat.card (E i) = Nat.card (P i) :=
    card_map_of_injective (L i).subtype_injective
  let Ω : Set (Subgroup G) := {A | IsElementaryAbelian 2 A ∧
    ∃ i, A.map q ≤ L i ∧ Nat.card (A.map q) = Nat.card (P i)}
  have hΩ : IsElementaryFamily Ω := by
    refine ⟨fun A hA => hA.1,?_⟩
    rintro g A ⟨ha,i,hi,hc⟩
    let := ha
    obtain ⟨j,hj⟩ := hperm (q g) i
    have he : (A.map (MulAut.conj g).toMonoidHom).map q =
        (A.map q).map (MulAut.conj (q g)).toMonoidHom := by
      rw [map_map,map_map]
      congr 1
      ext x
      simp [MulAut.conj_apply]
    refine ⟨IsElementaryAbelian.map _,j,?_,?_⟩
    · rw [he,←hj]
      exact map_mono hi
    · rw [he,card_map_of_injective (MulAut.conj (q g)).injective,hc,hcard i j]
  have huniq : ∀ A ∈ Ω, A ≤ (T : Subgroup G) → ∃ i, A.map q = E i := by
    rintro A ⟨_,i,hi,hc⟩ hAT
    refine ⟨i,eq_of_le_of_card_ge ?_ ?_⟩
    · change A.map q ≤ (P i : Subgroup (L i)).map (L i).subtype
      rw [hP i]
      exact le_inf (map_mono hAT) hi
    · rw [hcE i,hc]
  have hw : (weakClosure (T : Subgroup G) Ω).map q = B := by
    apply le_antisymm
    · apply map_le_iff_le_comap.mpr
      apply sSup_le
      rintro A ⟨ha,hAT⟩
      obtain ⟨i,hi⟩ := huniq A ha hAT
      exact map_le_iff_le_comap.mp (hi ▸ hEB i)
    · change (T : Subgroup G).map q ⊓ Y ≤ _
      rw [hspan]
      apply iSup_le
      intro i
      obtain ⟨A,ha,hAT,hi⟩ := hlift i
      rw [←hi]
      apply map_mono
      exact le_sSup ⟨⟨ha,i,hi ▸ map_subtype_le _,hi ▸ hcE i⟩,hAT⟩
  have hN : normalizer (B : Set Q) ≠ ⊤ := by
    intro hn
    have hBn : B.Normal := normalizer_eq_top_iff.mp hn
    have hBc : B ≤ pCore 2 Q := le_sSup ⟨hBn,S.isPGroup'.to_le inf_le_left⟩
    have hE : E 0 = ⊥ := bot_unique ((hEB 0).trans (hcore ▸ hBc))
    have hPz : (P 0 : Subgroup (L 0)) = ⊥ :=
      (map_eq_bot_iff_of_injective _ (L 0).subtype_injective).mp hE
    have hc : Nat.card (P 0) = 1 := card_eq_one.mpr hPz
    let : Subsingleton (P 0) := (Nat.card_eq_one_iff_unique.mp hc).1
    have hh := hr 0
    rw [Group.rank_eq_zero] at hh
    omega
  let M := (normalizer (B : Set Q)).comap q
  have hM : M ≠ ⊤ := by
    intro hm
    apply hN
    have hh := congrArg (map q) hm
    change ((normalizer (B : Set Q)).comap q).map q = (⊤ : Subgroup G).map q at hh
    simpa only [map_comap_eq_self_of_surjective hq,map_top_of_surjective q hq] using hh
  apply not_isEGenerated_of_members_le T Ω hΩ M hM
  · apply map_le_iff_le_comap.mp
    exact (le_normalizer_map q).trans (by rw [hw])
  · intro A ha hAT K hK
    obtain ⟨i,hi⟩ := huniq A ha hAT
    have hAB : A.map q ≤ B := hi ▸ hEB i
    have hBC : B ≤ centralizer (A.map q : Set Q) :=
      (le_centralizer_iff_isMulCommutative.mpr hcomm).trans (centralizer_le hAB)
    have htau := sylow_intersection_le_map_tau T q A hAT hker B inf_le_left hBC
    exact member_le_normalizer_of_pair_lift q hq T Y L P hLY hP hproper hperm
      hLs hLn r hr A K hK i hi htau

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.PairLift
