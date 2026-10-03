module
public import Stellmacher.PushingUp.SL2TwoNormalModule
public import Stellmacher.SectionTwo.TwoFourGeneratingCoordinate
public import Stellmacher.SectionTwo.TwoFourHallTransfer

/-!
# A core-residual bound retaining a prescribed module

Let V be normal elementary abelian, inside B≤S. Suppose B is Sylow in a
normal subgroup L with LS=G, and G has a unique maximal subgroup above S.
The quotient action on V has nontrivial B-image; its L-image is a product
of SL₂(2) factors. Assume the characteristic-Sylow obstruction for every
local subgroup with Sylow image B that generates G together with S.
Then [O₂(G),O²(G)] lies in this same prescribed V.

The full-image coordinate lift selects a generating local group K with
the required nested Frattini quotient. Its image contains an SL₂(2) factor,
so is not a two-group, and its Sylow image is the nontrivial image of B.
The normal-module pushing-up theorem therefore bounds K's local commutator
inside V. The Hall residual transfer propagates that bound to G.

This is the local-factor route in Stellmacher (2.4), Journal of Algebra
190 (1997), p20, adapted to preserve the original V in the application
in (4.6), p26. Local characteristic rigidity is explicit: it is not replaced
by an unproved characteristic-subgroup condition on the ambient Sylow.
-/

namespace Stellmacher.SectionTwo

/-- The selected SL₂(2) coordinate bounds the ambient core-residual commutator
inside the original prescribed module. -/
public theorem core_residual_le_prescribed_module
    {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (hsolv : Group.IsSolvable G) (S : Sylow 2 G)
    (V L B : Subgroup G) [V.Normal] [L.Normal]
    (hVe : IsElementaryAbelian 2 V) (hVB : V ≤ B) (hBS : B ≤ (S : Subgroup G))
    (PL : Sylow 2 L) (hPL : PL.map L.subtype = B)
    (hgen : L ⊔ (S : Subgroup G) = ⊤)
    (hunique : IsUniqueMaximalContaining (S : Subgroup G) (⊤ : Subgroup G))
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = Subgroup.centralizer (V : Set G))
    (hBne : B.map q ≠ ⊥)
    (hBinf : B.map q = ((S : Subgroup G).map q) ⊓ L.map q)
    {n : ℕ} (D : Fin n → Subgroup H)
    (hprod : IsInternalDirectProductFamily (L.map q) D)
    (hSL : ∀ i, IsSL2Two (D i))
    (hcharacteristic : ∀ (K : Subgroup G) (PK : Sylow 2 K),
      PK.map K.subtype = B → K ⊔ (S : Subgroup G) = ⊤ →
      ∀ A : Subgroup PK, A.Characteristic → A ≠ ⊥ →
        ¬ (A.map (PK : Subgroup K).subtype).Normal) :
    ⁅pCore 2 G, twoResidualAmbient (⊤ : Subgroup G)⁆ ≤ V := by
  let T := S.mapSurjective hq
  have hEN : (L.map q).Normal := Subgroup.Normal.map inferInstance q hq
  obtain ⟨K, PK, i, hBK, hKL, hPK, hA, hKgen, hKimage⟩ :=
    exists_generating_coordinate_frattini_lift_with_image hsolv S T q hq
      (B.map q) (L.map q) B L PL hPL rfl hBinf hBne rfl hgen hunique hEN D hprod hSL
  have hVK : V ≤ K := hVB.trans hBK
  let VK := V.subgroupOf K
  let _ : VK.Normal := Subgroup.Normal.subgroupOf inferInstance K
  have hVKP : VK ≤ (PK : Subgroup K) := by
    apply (Subgroup.map_le_map_iff_of_injective K.subtype_injective).mp
    rw [hPK, Subgroup.map_subgroupOf_eq_of_le hVK]
    exact hVB
  let f := q.comp K.subtype
  have hfker : f.ker = Subgroup.centralizer (VK : Set K) := by
    ext k
    change (k : G) ∈ q.ker ↔ k ∈ Subgroup.centralizer (VK : Set K)
    rw [hker, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro hk v hv
      exact Subtype.ext (hk (v : G) hv)
    · intro hk v hv
      exact congrArg Subtype.val (hk ⟨v, hVK hv⟩ hv)
  have hPKimage : (PK : Subgroup K).map f = B.map q := by
    change (PK : Subgroup K).map (q.comp K.subtype) = _
    rw [← Subgroup.map_map, hPK]
  have hfrange : f.range = K.map q := by
    change (q.comp K.subtype).range = _
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hfnot : ¬ IsPGroup 2 f.range := by
    intro hp
    have hDi : D i ≤ f.range := by
      rw [hfrange, hKimage]
      exact le_sup_left
    have hpD : IsPGroup 2 (D i) := hp.to_le hDi
    have hcard : Nat.card (D i) = 6 :=
      Stellmacher.SectionOne.RankOneThreeGroupAssembly.isSL2Two_card (hSL i)
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := 2)).mp hpD
    rw [hcard] at hm
    have hdiv : 3 ∣ 2 ^ m := by omega
    have h := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdiv
    norm_num at h
  have hlocalNative := Stellmacher.PushingUp.sl2Two_localCommutator_le_normal_module
    PK (hcharacteristic K PK hPK hKgen) hA VK hVKP f hfker
      (hPKimage ▸ hBne) hfnot
  have hlocal : (⁅pCore 2 K, twoResidualAmbient (⊤ : Subgroup K)⁆).map K.subtype ≤ V := by
    have hm := Subgroup.map_mono (f := K.subtype) hlocalNative
    rwa [Subgroup.map_subgroupOf_eq_of_le hVK] at hm
  have hVL : V ≤ L := hVB.trans (hPL ▸ Subgroup.map_subtype_le _)
  exact two_four_hall_residual_transfer hsolv S V L K B inferInstance inferInstance hVe
    hVL hBS PL hPL PK hPK hKL hKgen hlocal

end Stellmacher.SectionTwo
