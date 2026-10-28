module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryRootCentralization
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.RootScalars
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.GoodCentralizers.Geometry
public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Even.BenderTwoKernel
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.Torus
public import Theory.GroupTheory.EmbeddedCenterMap
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryComponentSylow
public import Theory.GroupTheory.SylowNormalizerCentralQuotient

/-!
# Cartan obstructions and the original component Sylow normalizer

The full Sylow normalizer acts transitively on nonidentity Sylow-center
vectors in the Bender and linear-three rows. A central elementary sixteen
therefore has centralizer index at least fifteen. For Sp₄ the actual
Cartan weights are a² and ab. Above field order four a scalar subtorus
already gives index at least seven. At order four the sixteen is the whole
central root plane, on which the Cartan acts faithfully with order nine.
This includes degree three without imposing a false field restriction.

The last theorem returns to the original ambient group. A surjection
carries the original component Sylow normalizer onto the quotient Sylow
normalizer. The marked inner action transports its centralizer bound.
If the original normalizer preserved the whole doubled orbit, the literal
paired-plane S₃ action would bound this index by six, a contradiction.
Thus every such classical component has an original Sylow normalizer
escaping the orbit normalizer. NonFFSourceDoubledBinaryCartan applies this
to the chosen module and identifies its orbit normalizer with M=N_G(L).

Source: Aschbacher–Smith, proof of 7.7.6, printed p.706,
refs/quasithin.pdf. This is the Cartan obstruction, not the missing ambient
Borel placement. Exceptional root groups, central-cover lifting and the
local C(G,T) argument remain with qt-d-1222-nonff-doubled.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryCartan
open DoubledBinaryRootCentralization
private theorem transitive_index_bound {G : Type*} [Group G] [Finite G]
    (N Z A : Subgroup G) (hAZ : A ≤ Z) (hA : A ≠ ⊥)
    (htrans : ∀ a ∈ Z, a ≠ 1 → ∀ b ∈ Z, b ≠ 1 →
      ∃ n ∈ N, n * a * n⁻¹ = b) :
    Nat.card Z - 1 ≤ ((centralizer (A : Set G)).subgroupOf N).index := by
  classical
  let : MulAction N G := MulAction.compHom G ((MulAut.conj : G →* MulAut G).comp N.subtype)
  obtain ⟨a,ha,ha1⟩ := (A.bot_or_exists_ne_one).resolve_left hA
  have hstab : MulAction.stabilizer N a = (centralizer ({a} : Set G)).subgroupOf N := by
    ext n
    change (n : G) * a * (n : G)⁻¹ = a ↔ _
    rw [mem_subgroupOf,mem_centralizer_singleton_iff,mul_inv_eq_iff_eq_mul]
  let r : {z : Z // z ≠ 1} → MulAction.orbit N a := fun z =>
    ⟨z.val.val,by
      obtain ⟨n,hn,he⟩ := htrans a (hAZ ha) ha1 z.val z.val.property
        (fun hh => z.property (Subtype.ext hh))
      exact ⟨⟨n,hn⟩,he⟩⟩
  have hr : Function.Injective r := by
    intro x y he
    exact Subtype.ext (Subtype.ext (congrArg (fun z : MulAction.orbit N a => (z : G)) he))
  have hc : Nat.card {z : Z // z ≠ 1} = Nat.card Z - 1 := by
    let := Fintype.ofFinite Z
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    simp [Nat.card_eq_fintype_card]
  have hbound := Nat.card_le_card_of_injective r hr
  rw [hc,Nat.card_congr (MulAction.orbitEquivQuotientStabilizer N a),
    ←index_eq_card,hstab] at hbound
  apply hbound.trans
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero (index_ne_zero_of_finite))
    (index_dvd_of_le (comap_mono (centralizer_le (Set.singleton_subset_iff.mpr ha))))
/-- The complete Bender normalizer moves the projected sixteen with index
at least fifteen, using its actual action on the Sylow center. -/
theorem bender_normalizer_index {G : Type*} [Group G] [Finite G]
    (hm : ClassificationModels.IsBenderModel G) (P : Sylow 2 G)
    (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hAP : A ≤ (P : Subgroup G)) (hA : Nat.card A = 16) :
    15 ≤ ((centralizer (A : Set G)).subgroupOf (normalizer (P : Set G))).index := by
  let hb := Chapter1.QuasisimpleInvolutions.isSimpleBenderGroup_of_benderModel hm
  obtain ⟨n,_,_,hw,_⟩ := Chapter2.BenderFusion.GoodCentralizers.exponent_and_omega_of_simpleBender hb P
  have hN := Chapter2.BenderFusion.GoodCentralizers.normalizer_omega_eq hb P hw
  have ht := (Chapter2.BenderFusion.OmegaNormalizerModels.of_bender_model hm P).transitive
  rw [hN,hw] at ht
  have hAZ := bender_centralizes hm P A hAP
  have hAn : A ≠ ⊥ := by intro he; rw [he,card_bot] at hA; omega
  have hc := transitive_index_bound (normalizer (P : Set G)) _ A hAZ hAn ht
  have hs := Nat.card_le_card_of_injective (inclusion hAZ) (inclusion_injective hAZ)
  rw [hA] at hs
  omega

/-- In the nonbinary linear-three row the full actual Sylow normalizer
has centralizer index at least fifteen on the projected moving sixteen. -/
theorem linear_normalizer_index {G : Type*} [Group G] [Finite G]
    {n : ℕ} (hn : 2 ≤ n) (hm : ClassicalGroup.IsPSL G 3 (2 ^ n))
    (P : Sylow 2 G) (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hAP : A ≤ (P : Subgroup G)) (hA : Nat.card A = 16)
    (hi : ((centralizer (A : Set G)).subgroupOf (P : Subgroup G)).index ≤ 2) :
    15 ≤ ((centralizer (A : Set G)).subgroupOf (normalizer (P : Set G))).index := by
  have hAZ := linear_centralizes hn hm P A hAP hi
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  have ht := Matrix.PSL3.LinearThree.RootScalars.sylow_center_nonidentity_transitive F
    (by omega) hF e P
  have hAn : A ≠ ⊥ := by intro he; rw [he,card_bot] at hA; omega
  have hc := transitive_index_bound (normalizer (P : Set G)) _ A hAZ hAn ht
  have hs := Nat.card_le_card_of_injective (inclusion hAZ) (inclusion_injective hAZ)
  rw [hA] at hs
  omega

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryCartan

end

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryCartan
open Theory.SpecificGroups.SymplecticFour
open CentralRootGeometry
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private def torusInNormalizer : (Fˣ × Fˣ) →* normalizer (unipotent (F := F) : Set (Sp F)) :=
  diagonalTorusHom.codRestrict _ diagonalTorus_normalizes

private theorem index_comap_le {X Y : Type*} [Group X] [Group Y] [Finite Y]
    (C : Subgroup Y) (f : X →* Y) : (C.comap f).index ≤ C.index := by
  rw [C.index_comap]
  exact (relIndex_le_of_le_right (H := C) (le_top : f.range ≤ ⊤)
    (by simpa using C.index_ne_zero_of_finite)).trans_eq C.relIndex_top_right

omit [Finite F] in
private theorem diagonal_fixed {a : Fˣ} {s t : F}
    (hs : s ≠ 0 ∨ t ≠ 0)
    (hc : Commute (diagonalTorusHom (a,a))
      (parameter (Multiplicative.ofAdd s,Multiplicative.ofAdd t))) : a = 1 := by
  have hh := hc.mul_inv_cancel
  rw [diagonalTorus_weights] at hh
  have hp := parameter_injective hh
  have ha : (a : F)^2 = 1 := by
    rcases hs with hs | ht
    · have hh := congrArg (fun z : Multiplicative F × Multiplicative F => z.1.toAdd) hp
      exact mul_right_cancel₀ hs (hh.trans (one_mul _).symm)
    · have hh := congrArg (fun z : Multiplicative F × Multiplicative F => z.2.toAdd) hp
      change (a : F) * (a : F) * t = t at hh
      exact mul_right_cancel₀ ht ((show (a : F)^2*t=t by simpa only [pow_two] using hh).trans
        (one_mul _).symm)
  exact Units.ext (CharTwo.sq_injective (by simpa using ha))

private theorem scalar_index_bound
    (A : Subgroup (Sp F)) (hAn : A ≠ ⊥)
    (hAZ : A ≤ (center (unipotent (F := F))).map unipotent.subtype) :
    Nat.card F - 1 ≤ ((centralizer (A : Set (Sp F))).subgroupOf
      (normalizer (unipotent (F := F) : Set (Sp F)))).index := by
  let C := (centralizer (A : Set (Sp F))).subgroupOf (normalizer (unipotent (F := F) : Set (Sp F)))
  let d : Fˣ →* normalizer (unipotent (F := F) : Set (Sp F)) :=
    torusInNormalizer.comp ((MonoidHom.id _).prod (MonoidHom.id _))
  obtain ⟨a,ha,ha1⟩ := (A.bot_or_exists_ne_one).resolve_left hAn
  have hpar := hAZ ha
  rw [←parameter_range] at hpar
  obtain ⟨⟨s,t⟩,rfl⟩ := hpar
  have hst : s.toAdd ≠ 0 ∨ t.toAdd ≠ 0 := by
    by_contra hn
    simp only [not_or,not_not] at hn
    apply ha1
    have he : (s,t) = (1 : Multiplicative F × Multiplicative F) := Prod.ext hn.1 hn.2
    rw [he,map_one]
  have hk : C.comap d = ⊥ := by
    apply bot_unique
    intro a haC
    apply diagonal_fixed hst
    exact (haC _ ha).symm
  have hi := index_comap_le C d
  rw [hk,index_bot,Nat.card_units] at hi
  exact hi

private theorem full_center_index_bound :
    (Nat.card F - 1)^2 ≤
      ((centralizer ((center (unipotent (F := F))).map unipotent.subtype : Set (Sp F))).subgroupOf
        (normalizer (unipotent (F := F) : Set (Sp F)))).index := by
  let C := (centralizer ((center (unipotent (F := F))).map unipotent.subtype : Set (Sp F))).subgroupOf
    (normalizer (unipotent (F := F) : Set (Sp F)))
  have hmem (s t : F) : parameter (Multiplicative.ofAdd s,Multiplicative.ofAdd t) ∈
      (center (unipotent (F := F))).map unipotent.subtype := by
    rw [←parameter_range]
    exact ⟨_,rfl⟩
  have hk : C.comap (torusInNormalizer (F := F)) = ⊥ := by
    apply bot_unique
    intro a haC
    have hfix (s t : F) :
        parameter (Multiplicative.ofAdd ((a.1:F)^2*s),
          Multiplicative.ofAdd ((a.1:F)*(a.2:F)*t)) =
        parameter (Multiplicative.ofAdd s,Multiplicative.ofAdd t) := by
      have hh := mul_inv_eq_iff_eq_mul.mpr (haC _ (hmem s t)).symm
      exact (diagonalTorus_weights a s t).symm.trans hh
    have h1 := congrArg (fun z : Multiplicative F × Multiplicative F => z.1.toAdd)
      (parameter_injective (hfix 1 0))
    have ha1 : a.1 = 1 := Units.ext (CharTwo.sq_injective (by simpa using h1))
    have h2 := congrArg (fun z : Multiplicative F × Multiplicative F => z.2.toAdd)
      (parameter_injective (hfix 0 1))
    have ha2 : a.2 = 1 := Units.ext (by simpa [ha1] using h2)
    exact Prod.ext ha1 ha2
  have hi := index_comap_le C (torusInNormalizer (F := F))
  rw [hk,index_bot,Nat.card_prod,Nat.card_units,←pow_two] at hi
  exact hi

private theorem standard_symplectic_index {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2^n)
    (A : Subgroup (Sp F)) (hA : Nat.card A = 16)
    (hAZ : A ≤ (center (unipotent (F := F))).map unipotent.subtype) :
    7 ≤ ((centralizer (A : Set (Sp F))).subgroupOf
      (normalizer (unipotent (F := F) : Set (Sp F)))).index := by
  by_cases hn2 : n = 2
  · subst n
    have hc : Nat.card ((center (unipotent (F := F))).map unipotent.subtype) = 16 := by
      rw [card_map_of_injective unipotent.subtype_injective,
        ←Nat.card_congr (centerEquiv (F := F)).toEquiv,Nat.card_prod,
        Nat.card_congr Multiplicative.toAdd,hF]
      rfl
    have he := eq_of_le_of_card_ge hAZ (hc.trans hA.symm).le
    rw [he]
    have hi := full_center_index_bound (F := F)
    rw [hF] at hi
    norm_num only [Nat.reducePow, Nat.reduceSub] at hi
    omega
  · have hAn : A ≠ ⊥ := by intro he; rw [he,card_bot] at hA; omega
    have hi := scalar_index_bound A hAn hAZ
    have hbig := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (show 3 ≤ n by omega)
    rw [hF] at hi
    norm_num at hbig
    omega
private theorem centralizer_map_equiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (A : Subgroup G) :
    (centralizer (A : Set G)).map e.toMonoidHom = centralizer (A.map e.toMonoidHom : Set H) := by
  apply le_antisymm (map_centralizer_le_centralizer_image (A : Set G) e.toMonoidHom)
  intro x hx
  obtain ⟨y,rfl⟩ := e.surjective x
  refine ⟨y,?_,rfl⟩
  intro a ha
  apply e.injective
  simpa only [map_mul] using hx (e a) (mem_map_of_mem e.toMonoidHom ha)

/-- The genuine symplectic Cartan action has index greater than three on
the moving sixteen. At q=4 that sixteen is the full Sylow center; at
larger fields the scalar subtorus alone gives the required bound. -/
theorem symplectic_normalizer_index {G : Type*} [Group G] [Finite G]
    {n : ℕ} (hn : 2 ≤ n) (hm : ClassicalGroup.IsPSp G 2 (2 ^ n))
    (P : Sylow 2 G) (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hAP : A ≤ (P : Subgroup G)) (hA : Nat.card A = 16)
    (hi : ((centralizer (A : Set G)).subgroupOf (P : Subgroup G)).index ≤ 2) :
    7 ≤ ((centralizer (A : Set G)).subgroupOf (normalizer (P : Set G))).index := by
  have hAZ := DoubledBinaryRootCentralization.symplectic_centralizes hn hm P A hAP hi
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : CharP F 2 := EvenProjective.charTwo_of_card hF
  let e' : Sp F ≃* G := EvenProjective.equiv.trans e.symm
  let P₀ := (unipotentSylow hF (by omega)).mapSurjective (f := e'.toMonoidHom) e'.surjective
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G P₀ P
  let f := e'.trans (MulAut.conj g)
  have hP : (unipotent (F := F)).map f.toMonoidHom = (P : Subgroup G) := by
    have hh := congrArg Sylow.toSubgroup hg
    change ((unipotent (F := F)).map e'.toMonoidHom).map
      (MulAut.conj g).toMonoidHom = (P : Subgroup G) at hh
    change (unipotent (F := F)).map ((MulAut.conj g).toMonoidHom.comp e'.toMonoidHom) = _
    rw [←map_map]
    exact hh
  have hZ : ((center (unipotent (F := F))).map unipotent.subtype).map f.toMonoidHom =
      (center P).map (P : Subgroup G).subtype := by
    rw [map_embeddedCenter _ _ f.injective,hP]
  let A₀ := A.map f.symm.toMonoidHom
  have hA₀ : A₀.map f.toMonoidHom = A := by
    change (A.map f.symm.toMonoidHom).map f.toMonoidHom = A
    rw [map_map]
    rw [show f.toMonoidHom.comp f.symm.toMonoidHom = MonoidHom.id _ by
      ext x; exact f.apply_symm_apply x, map_id]
  have hAZ₀ : A₀ ≤ (center (unipotent (F := F))).map unipotent.subtype := by
    apply (map_le_map_iff_of_injective (f := f.toMonoidHom) f.injective).mp
    rw [hA₀,hZ]
    exact hAZ
  have hcard : Nat.card A₀ = 16 := (card_map_of_injective f.symm.injective).trans hA
  have hb := standard_symplectic_index hn hF A₀ hcard hAZ₀
  have hN : (normalizer (unipotent (F := F) : Set (Sp F))).map f.toMonoidHom =
      normalizer (P : Set G) := by
    rw [map_equiv_normalizer_eq,hP]
    rfl
  have hC : (centralizer (A₀ : Set (Sp F))).map f.toMonoidHom = centralizer (A : Set G) := by
    rw [centralizer_map_equiv,hA₀]
  change 7 ≤ (centralizer (A : Set G)).relIndex (normalizer (P : Set G))
  rw [←hC,←hN,relIndex_map_map_of_injective _ _ f.injective]
  exact hb
end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryCartan

end

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryCartan

private theorem inner_conj {K : Type*} [Group K] (k : K) :
    innerEquivCentralQuotient ((MulAut.conj : K →* MulAut K).rangeRestrict k) =
      (QuotientGroup.mk' (center K)) k := by
  change QuotientGroup.quotientMulEquivOfEq DoubleCoverCentralizer.conj_kernel
    ((QuotientGroup.quotientKerEquivRange (MulAut.conj : K →* MulAut K)).symm
      (MulAut.conj.rangeRestrict k)) = _
  have he : (QuotientGroup.quotientKerEquivRange (MulAut.conj : K →* MulAut K)).symm
      (MulAut.conj.rangeRestrict k) = QuotientGroup.mk k := by
    apply (QuotientGroup.quotientKerEquivRange (MulAut.conj : K →* MulAut K)).injective
    rw [MulEquiv.apply_symm_apply]
    rfl
  rw [he]
  rfl

/-- A large centralizer index in the actual quotient Sylow normalizer
forces the original component Sylow normalizer to escape the orbit normalizer.
The S₃ bound comes from the literal paired-plane action; the quotient map
and inner-action marking are the original ones. -/
theorem normalizer_escape
    {G : Type*} [Group G] [Finite G] (W U K A : Subgroup G)
    (hAW : A ≤ W) (hKC : K ≤ centralizer (U : Set G))
    (hAN : A ≤ normalizer (K : Set G))
    (he : Nonempty (ChapterE.inducedAutomizer W (centralizer (U : Set G)) ≃* Equiv.Perm (Fin 3)))
    (j : A →* K ⧸ center K)
    (hact : ∀ a : A, (innerEquivCentralQuotient.symm (j a) : MulAut K) =
      K.normalizerMonoidHom (inclusion hAN a))
    (P : Sylow 2 K)
    (hlarge : let Q := P.mapSurjective (QuotientGroup.mk'_surjective (center K))
      6 < ((centralizer (j.range : Set (K ⧸ center K))).subgroupOf
        (normalizer (Q : Set (K ⧸ center K)))).index) :
    ¬ (normalizer (P : Set K)).map K.subtype ≤ normalizer (W : Set G) := by
  intro hN
  let X := K ⧸ center K
  let q := QuotientGroup.mk' (center K)
  let Q := P.mapSurjective (QuotientGroup.mk'_surjective (center K))
  let N := normalizer (P : Set K)
  let NQ := normalizer (Q : Set X)
  let C := (centralizer (j.range : Set X)).subgroupOf NQ
  let B := normalizer (W : Set G) ⊓ centralizer (U : Set G)
  obtain ⟨π,_,hker⟩ := DoubledBinaryPlaneQuotient.centralizer_quotient W U he
  let f : N →* B := (K.subtype.comp N.subtype).codRestrict B
    (fun x => ⟨hN (mem_map_of_mem K.subtype x.property),hKC x.val.property⟩)
  let r := π.comp f
  have hmap : N.map q = NQ := P.normalizer_map_surjective q (QuotientGroup.mk'_surjective _)
  let g : N →* NQ := (MulEquiv.subgroupCongr hmap).toMonoidHom.comp (q.subgroupMap N)
  have hg : Function.Surjective g :=
    (MulEquiv.subgroupCongr hmap).surjective.comp (q.subgroupMap_surjective N)
  have hk : r.ker ≤ C.comap g := by
    intro n hn
    have hnW : (n.val : G) ∈ centralizer (W : Set G) := by
      have hh : f n ∈ π.ker := hn
      rw [hker] at hh
      exact hh
    change q n.val ∈ centralizer (j.range : Set X)
    rintro _ ⟨a,rfl⟩
    let e := innerEquivCentralQuotient (H := K)
    have hf : (e.symm (j a) : MulAut K) n.val = n.val := by
      rw [hact a]
      apply Subtype.ext
      change (a : G) * (n.val : G) * (a : G)⁻¹ = (n.val : G)
      exact mul_inv_eq_iff_eq_mul.mpr (hnW a (hAW a.property))
    have hq : e.symm (q n.val) = (MulAut.conj : K →* MulAut K).rangeRestrict n.val := by
      apply e.injective
      rw [e.apply_symm_apply,inner_conj]
    apply e.symm.injective
    rw [map_mul,map_mul,hq]
    apply Subtype.ext
    apply MulEquiv.ext
    intro x
    change (e.symm (j a) : MulAut K) (n.val * x * n.val⁻¹) =
      n.val * (e.symm (j a) : MulAut K) x * n.val⁻¹
    rw [map_mul,map_mul,map_inv,hf]
  have hsmall : r.ker.index ≤ 6 := by
    rw [index_ker]
    have hc := Nat.card_le_card_of_injective r.range.subtype r.range.subtype_injective
    simpa only [Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin,
      show Nat.factorial 3 = 6 by decide] using hc
  have hc : C.index ≤ 6 := by
    rw [←C.index_comap_of_surjective hg]
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero (index_ne_zero_of_finite))
      (index_dvd_of_le hk)).trans hsmall
  exact (not_lt_of_ge hc) hlarge
end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryCartan

end
