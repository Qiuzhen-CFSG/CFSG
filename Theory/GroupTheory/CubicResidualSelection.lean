module
public import Theory.GroupTheory.SymmetricThreeCentralKernel
public import Theory.GroupTheory.NormalSubgroupCoreQuotient
public import Theory.GroupTheory.GeneralizedFitting.ResidualCentralizer
public import Theory.GroupTheory.NormalSymmetricThreePairRank
public import Theory.GroupTheory.PResidual.CoreCentralizer
public import Theory.Quasithin.Rank

/-!
# One Thompson factor above a cubic residual section

Let K and I be normal in H, with O₂(H) ≤ K, and let D be the embedded
O²(K). Suppose D/O₂(D) has order three, I centralizes that section,
and the image of I in H/K is S₃ or S₃ × S₃. If I is three-perfect,
central cubic kernel elimination shows that I ∩ K ≤ O₂(H). After removing
the two-core, the residual D is an independent cubic subgroup centralizing I.
Ambient three-rank at most two therefore excludes two factors.

The proof uses the actual map H/O₂(H) → H/K and normal-subgroup core
restriction. It proves I/O₂(I) ≅ S₃ without assuming K = O₂(H).
In the source application, three-perfectness comes from the two-group
seed J(R₁), and section centralization comes from 13.4.4(ii).
Source: Aschbacher–Smith 13.4.8, printed p.905.
-/

public noncomputable section

namespace Theory.GroupTheory.CubicResidualSelection
open Subgroup
variable {H : Type*} [Group H] [Finite H]
local notation "S3" => Equiv.Perm (Fin 3)

/-- With trivial ambient two-core, section-centralizing kernel elements lie in the residual. -/
theorem kernel_le_residual (K I : Subgroup H) [K.Normal]
    (hcore : pCore 2 H = ⊥)
    (hIC : I ≤ centralizer ((pResidual 2 K).map K.subtype : Set H)) :
    I ⊓ K ≤ (pResidual 2 K).map K.subtype := by
  have hK : pCore 2 K = ⊥ := by
    rw [pCore_eq_comap_of_normal, hcore, MonoidHom.comap_bot]
    exact K.ker_subtype
  intro x hx
  have hc : (⟨x,hx.2⟩ : K) ∈ centralizer (pResidual 2 K : Set K) := by
    intro d hd
    exact Subtype.ext (hIC hx.1 d (mem_map_of_mem K.subtype hd))
  exact mem_map_of_mem K.subtype (centralizer_pResidual_le_of_pCore_eq_bot hK hc)

/-- The central cubic kernel vanishes in a three-perfect normal Thompson image;
ambient rank two then excludes two symmetric-three factors. -/
theorem single_of_cubic_residual (K I : Subgroup H) [K.Normal] [I.Normal]
    (hcore : pCore 2 H = ⊥) (hcard : Nat.card (pResidual 2 K) = 3)
    (hI : IsPPerfect 3 I)
    (hIC : I ≤ centralizer ((pResidual 2 K).map K.subtype : Set H))
    (hm : Nonempty ((I.map (QuotientGroup.mk' K)) ≃* S3) ∨
      Nonempty ((I.map (QuotientGroup.mk' K)) ≃* (S3 × S3)))
    (hrank : primeRank 3 H ≤ 2) : Nonempty (I ≃* S3) ∧ Disjoint I K := by
  let D := (pResidual 2 K).map K.subtype
  let q := QuotientGroup.mk' K
  let f := q.subgroupMap I
  have hD : Nat.card D = 3 := by rw [card_map_of_injective K.subtype_injective]; exact hcard
  have hKD := kernel_le_residual K I hcore hIC
  have hfc : f.ker ≤ center I := by
    intro x hx
    have hxK : (x : H) ∈ K := (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val hx)
    have hxD := hKD ⟨x.property,hxK⟩
    exact mem_center_iff.mpr fun y => Subtype.ext ((hIC y.property x hxD).symm)
  have hfp : IsPGroup 3 f.ker := by
    let g : f.ker →* D := (I.subtype.comp f.ker.subtype).codRestrict D (fun x =>
      hKD ⟨x.val.property,(QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val x.property)⟩)
    have hg : Function.Injective g := fun a b h => Subtype.ext (Subtype.ext
      (show (a : H) = (b : H) from congrArg (fun d : D => (d : H)) h))
    exact (IsPGroup.of_card (p := 3) (n := 1) (by simpa using hD)).of_injective g hg
  have hfb : f.ker = ⊥ := by
    rcases hm with he | he
    · obtain ⟨e⟩ := he
      have hh := SymmetricThreeCentralKernel.single (e.toMonoidHom.comp f)
        (e.surjective.comp (q.subgroupMap_surjective I))
        (by simpa only [MonoidHom.ker_comp_of_injective f e.toMonoidHom e.injective] using hfc)
        (hfp.of_equiv (MulEquiv.subgroupCongr
          (MonoidHom.ker_comp_of_injective f e.toMonoidHom e.injective).symm)) hI
      simpa only [MonoidHom.ker_comp_of_injective f e.toMonoidHom e.injective] using hh
    · obtain ⟨e⟩ := he
      have hh := SymmetricThreeCentralKernel.pair (e.toMonoidHom.comp f)
        (e.surjective.comp (q.subgroupMap_surjective I))
        (by simpa only [MonoidHom.ker_comp_of_injective f e.toMonoidHom e.injective] using hfc)
        (hfp.of_equiv (MulEquiv.subgroupCongr
          (MonoidHom.ker_comp_of_injective f e.toMonoidHom e.injective).symm)) hI
      simpa only [MonoidHom.ker_comp_of_injective f e.toMonoidHom e.injective] using hh
  let eI : I ≃* I.map q := MulEquiv.ofBijective f
    ⟨(MonoidHom.ker_eq_bot_iff f).mp hfb,q.subgroupMap_surjective I⟩
  have hd : Disjoint I K := by
    apply disjoint_def.mpr
    intro x hx hk
    have hfk : (⟨x,hx⟩ : I) ∈ f.ker :=
      Subtype.ext ((QuotientGroup.eq_one_iff _).mpr hk)
    exact congrArg Subtype.val (show (⟨x,hx⟩ : I) = 1 from (by rw [hfb] at hfk; exact hfk))
  refine ⟨?_,hd⟩
  rcases hm with he | he
  · obtain ⟨e⟩ := he
    exact ⟨eI.trans e⟩
  · obtain ⟨e⟩ := he
    have hn := NormalSymmetricThreePairRank.three_not_dvd_card_centralizer I (eI.trans e) hrank
    exact (hn (hD ▸ card_dvd_of_le (le_centralizer_iff.mp hIC))).elim

end Theory.GroupTheory.CubicResidualSelection

namespace Theory.GroupTheory.CubicResidualSelection
open Subgroup
variable {H : Type*} [Group H] [Finite H]
local notation "S3" => Equiv.Perm (Fin 3)

/-- The cubic residual-section argument applies before discarding the two-core. -/
theorem core_quotient_single (K I : Subgroup H) [K.Normal] [I.Normal]
    (hQK : pCore 2 H ≤ K)
    (hcard : let D := (pResidual 2 K).map K.subtype
      Nat.card (D ⧸ pCore 2 D) = 3)
    (hI : IsPPerfect 3 I)
    (hIC : let D := (pResidual 2 K).map K.subtype
      ⁅I,D⁆ ≤ D.pCoreIn 2)
    (hm : Nonempty ((I.map (QuotientGroup.mk' K)) ≃* S3) ∨
      Nonempty ((I.map (QuotientGroup.mk' K)) ≃* (S3 × S3)))
    (hrank : primeRank 3 H ≤ 2) :
    Nonempty ((I ⧸ pCore 2 I) ≃* S3) ∧ I ⊓ K ≤ pCore 2 H := by
  let Q := pCore 2 H
  let q := QuotientGroup.mk' Q
  let Kb := K.map q
  let Ib := I.map q
  let D := (pResidual 2 K).map K.subtype
  let Db := D.map q
  let : Kb.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let : Ib.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let : D.Normal := inferInstance
  have hDb : Db = (pResidual 2 Kb).map Kb.subtype := map_embedded_pResidual 2 K q
  have hcardb : Nat.card (pResidual 2 Kb) = 3 := by
    have hh : Nat.card Db = 3 := by
      rw [← Nat.card_congr (coreQuotientEquivImage 2 D).toEquiv]
      exact hcard
    rwa [hDb,card_map_of_injective Kb.subtype_injective] at hh
  have hDC : D.pCoreIn 2 ≤ Q :=
    show (pCore 2 D).map D.subtype ≤ Q from le_sSup ⟨inferInstance,pCore_isPGroup.map D.subtype⟩
  have hc : Ib ≤ centralizer ((pResidual 2 Kb).map Kb.subtype : Set (H ⧸ Q)) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [← hDb,← map_commutator]
    exact (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']; exact hIC.trans hDC)
  have hi : IsPPerfect 3 Ib := hI.of_surjective (q.subgroupMap I) (q.subgroupMap_surjective I)
  let qb := QuotientGroup.mk' Kb
  let eqQ : ((H ⧸ Q) ⧸ Kb) ≃* (H ⧸ K) :=
    QuotientGroup.quotientQuotientEquivQuotient Q K hQK
  have hmaps : (Ib.map qb).map eqQ.toMonoidHom = I.map (QuotientGroup.mk' K) := by
    rw [map_map,map_map]
    rfl
  let ei : Ib.map qb ≃* I.map (QuotientGroup.mk' K) :=
    ((Ib.map qb).equivMapOfInjective eqQ.toMonoidHom eqQ.injective).trans
      (MulEquiv.subgroupCongr hmaps)
  have hmb : Nonempty ((Ib.map qb) ≃* S3) ∨ Nonempty ((Ib.map qb) ≃* (S3 × S3)) := by
    rcases hm with he | he
    · obtain ⟨e⟩ := he; exact Or.inl ⟨ei.trans e⟩
    · obtain ⟨e⟩ := he; exact Or.inr ⟨ei.trans e⟩
  have hr : primeRank 3 (H ⧸ Q) ≤ 2 :=
    (primeRank_quotient_le_of_isTwoGroup 3 (by decide) Q pCore_isPGroup).trans hrank
  obtain ⟨he,hd⟩ := single_of_cubic_residual Kb Ib (pCore_quotient_pCore_eq_bot 2)
    hcardb hi hc hmb hr
  obtain ⟨e⟩ := he
  refine ⟨⟨(coreQuotientEquivImage 2 I).trans e⟩,?_⟩
  intro x hx
  exact (QuotientGroup.eq_one_iff _).mp
    (disjoint_def.mp hd (mem_map_of_mem q hx.1) (mem_map_of_mem q hx.2))

end Theory.GroupTheory.CubicResidualSelection
