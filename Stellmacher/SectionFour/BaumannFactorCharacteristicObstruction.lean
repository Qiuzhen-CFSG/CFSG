module

public import Stellmacher.SectionFour.NormalSupplement
public import Stellmacher.SectionFour.CharacteristicRigidity
public import Stellmacher.BaumannNormalizer

/-!
# Characteristic obstruction for a native Baumann factor in (4.6)

In the exact opening configuration of Stellmacher (4.6), let `B` be the
Baumann subgroup of `O₂(C)`, and let `K` be a subgroup native to `Pstar`.
For the supplied Sylow subgroups `PK` of `K` and `SP` of `Pstar`, assume
that their images are exactly `B.subgroupOf Pstar` and the original `S`,
and that `K ∨ SP = Pstar` internally. Then no nontrivial characteristic
subgroup of this same `PK` has normal image in `K`.

The normal-supplement data puts `B` inside `S`. Since `P ≤ C`, the core
and Baumann normalizer theorems show that `P` normalizes `B`. Map `K` to
its ambient image `L`; the generation hypothesis becomes `L ∨ S = Pstar`.
The exact composite inclusion identifies `PK` with `B` and transports its
characteristic subgroup to a characteristic subgroup of `B`. If its native
image were normal in `K`, the normalizer-map lemma would make its ambient
image normal inside `L`. The accepted critical-pair characteristic rigidity
then makes it trivial, and the injective image equivalence reflects this
back to the original subgroup of `PK`.

Source: Stellmacher, Journal of Algebra 190 (1997), proof of (4.6), p.26,
the characteristic obstruction used in the local application of (2.4), in
`refs/latex/stellmacher-n-group.tex`. The native Sylow witnesses are retained
exactly; the ambient critical join is handled by the imported rigidity theorem.
-/

open scoped Pointwise
namespace Stellmacher.SectionFour
universe u

public theorem baumann_factor_characteristic_obstruction
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (heven : Even (Nat.card G))
    (P Pstar E : Subgroup G) (hpair : (P, Pstar) ∈ Lambda S)
    (hPC : P ≤ cSubgroup S) (hEP : E ≤ Pstar)
    (hsolv : Group.IsSolvable Pstar) (hchar : IsCharacteristicTwoType Pstar)
    (hE : (E : Set G) = (twoResidualAmbient Pstar : Set G) *
      (twoCoreAmbient (cSubgroup S) : Set G))
    (hSyl : IsSylowSubgroupIn (twoCoreAmbient (cSubgroup S)) E) :
    let B := twoCoreAmbient (cSubgroup S) ⊓ Subgroup.centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ (twoCoreAmbient (cSubgroup S))) : Set G)
    ∀ (K : Subgroup Pstar) (PK : Sylow 2 K) (SP : Sylow 2 Pstar),
      (SP : Subgroup Pstar).map Pstar.subtype = (S : Subgroup G) →
      (PK : Subgroup K).map K.subtype = B.subgroupOf Pstar →
      K ⊔ (SP : Subgroup Pstar) = ⊤ →
      ∀ H : Subgroup PK, H.Characteristic → H ≠ ⊥ →
        ¬ (H.map (PK : Subgroup K).subtype).Normal := by
  classical
  dsimp only
  let B := twoCoreAmbient (cSubgroup S) ⊓ Subgroup.centralizer
    (omegaOneCenterAmbient (elementaryAbelianMaxJ (twoCoreAmbient (cSubgroup S))) : Set G)
  intro K PK SP hSPmap hPKmap hgen H hHchar hHne hHnormal
  obtain ⟨_, _, _, _, SP', QE, hSP', hQE, _, hQS, _, _⟩ :=
    baumann_normal_supplement_data S heven P Pstar E hpair hPC hEP hsolv hchar hE hSyl
  have hCoreS : twoCoreAmbient (cSubgroup S) ≤ (S : Subgroup G) := by
    have hm := Subgroup.map_mono (f := Pstar.subtype) hQS
    rwa [hQE, hSP'] at hm
  have hBS : B ≤ (S : Subgroup G) := inf_le_left.trans hCoreS
  have hBPstar : B ≤ Pstar := hBS.trans (hSPmap ▸ Subgroup.map_subtype_le _)
  have hPnormCore : P ≤ Subgroup.normalizer (twoCoreAmbient (cSubgroup S) : Set G) := by
    apply hPC.trans
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp
    rw [subgroupOf_map_subtype_eq]
    infer_instance
  have hPB : P ≤ Subgroup.normalizer (B : Set G) :=
    hPnormCore.trans (normalizer_le_normalizer_baumann _)
  let L : Subgroup G := K.map Pstar.subtype
  let f : K →* G := Pstar.subtype.comp K.subtype
  have hf : Function.Injective f := Pstar.subtype_injective.comp K.subtype_injective
  have hfRange : f.range = L := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hPKambient : (PK : Subgroup K).map f = B := by
    rw [← Subgroup.map_map, hPKmap, Subgroup.map_subgroupOf_eq_of_le hBPstar]
  have hBL : B ≤ L := by
    have hBK : B.subgroupOf Pstar ≤ K := by
      rw [← hPKmap]
      exact Subgroup.map_subtype_le _
    have hm := Subgroup.map_mono (f := Pstar.subtype) hBK
    rwa [Subgroup.map_subgroupOf_eq_of_le hBPstar] at hm
  have hLgen : Pstar ≤ L ⊔ (S : Subgroup G) := by
    have hm := congrArg (Subgroup.map Pstar.subtype) hgen
    rw [Subgroup.map_sup, hSPmap, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hm
    exact hm.symm.le
  let e : PK ≃* B := ((PK : Subgroup K).equivMapOfInjective f hf).trans
    (MulEquiv.subgroupCongr hPKambient)
  have he (x : PK) : ((e x : B) : G) = f (x : K) := by
    simp only [e, MulEquiv.trans_apply]
    rw [MulEquiv.subgroupCongr_apply]
    exact Subgroup.coe_equivMapOfInjective_apply _ _ _ x
  let HB : Subgroup B := H.map e.toMonoidHom
  have hHBchar : HB.Characteristic := by
    rw [Subgroup.characteristic_iff_map_le]
    intro φ x hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨k, hk, rfl⟩ := hy
    let ψ : PK ≃* PK := e.trans (φ.trans e.symm)
    have hψH := (Subgroup.characteristic_iff_map_le.mp hHchar) ψ
    exact ⟨ψ k, hψH ⟨k, hk, rfl⟩, e.apply_symm_apply _⟩
  have himage : HB.map B.subtype = (H.map (PK : Subgroup K).subtype).map f := by
    dsimp only [HB]
    rw [Subgroup.map_map, Subgroup.map_map]
    apply congrArg (fun g => H.map g)
    ext x
    exact he x
  have hXL : HB.map B.subtype ≤ L := (Subgroup.map_subtype_le _).trans hBL
  have hXN : ((HB.map B.subtype).subgroupOf L).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hXL).mpr
    rw [himage]
    let _ : (H.map (PK : Subgroup K).subtype).Normal := hHnormal
    have hnorm := (H.map (PK : Subgroup K).subtype).le_normalizer_map f
    rwa [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map, hfRange] at hnorm
  have hHBbot := critical_pair_characteristic_rigidity S P Pstar B L hpair hBS hPB
    hBL hLgen HB hHBchar hXN
  exact hHne ((Subgroup.map_eq_bot_iff_of_injective H (f := e.toMonoidHom) e.injective).mp hHBbot)

end Stellmacher.SectionFour
