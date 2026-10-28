module

public import Theory.GroupTheory.ComponentLocalOrbitCore
public import Theory.GroupTheory.ComponentLocalOrbitFactors
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Ree.LocalPair

/-!
# Characteristic-two cores and layers in the large Ree local orbit

A local seed invariant under N_S(L) gives a member of HeOver after adjoining
all of S. The proof takes the orbit inside H, where component subnormality
is given, and transports its normal two-core and centralizer calculations
to the common ambient group. Simplicity of L and containment of S ∩ L are
not needed for this core calculation.

A block's two-perfection places it in the local orbit. For a perfect seed
simple modulo its two-core, the subnormal-product calculation supplies a
conjugate seed factor inside every nontrivial block. Intersecting the block
with the actual two-core of the overgroup constructs a normal two-subgroup.
The seed's nonzero third commutator remains nonzero in that intersection.
The factor-containment calculation is transported from H, retaining the
relative subnormality and the actual embeddings of all conjugates.

These are conditional calculations for Aschbacher–Smith 2.3.9(7), printed
p.526; the Ree seed construction and final exclusion remain with the parent.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Ree
variable {G : Type*} [Group G]

/-- An invariant characteristic-two local seed gives a member of HeOver.
The stabilizer invariance permits the whole Sylow subgroup to permute components. -/
theorem local_overgroup_mem_HeOver {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (K : Subgroup L)
    (hinv : (S : Subgroup H).map H.subtype ⊓ normalizer (L : Set G) ≤
      normalizer (K.map L.subtype : Set G))
    (hne : pCore 2 K ≠ ⊥)
    (hself : centralizer (pCore 2 K : Set K) ≤ pCore 2 K) :
    K.map L.subtype ⊔ (S : Subgroup H).map H.subtype ∈
      Chapter1.HeOver G (((S : Subgroup H).map H.subtype : Subgroup G) : Set G) := by
  let := h.finite
  let P := K.map L.subtype
  let F := P.subgroupOf H
  have hPH : P ≤ H := (map_subtype_le K).trans h.component_le
  have hFL : F ≤ L.subgroupOf H := fun _ hx => map_subtype_le K hx
  have hmF : F.map H.subtype = P := map_subgroupOf_eq_of_le hPH
  have hinvH : (S : Subgroup H) ⊓ normalizer (L.subgroupOf H : Set H) ≤
      normalizer (F : Set H) := by
    rw [← subgroupOf_normalizer_eq h.component_le]
    change (S : Subgroup H) ⊓ (normalizer (L : Set G)).subgroupOf H ≤
      normalizer (P.subgroupOf H : Set H)
    rw [← subgroupOf_normalizer_eq hPH]
    intro x hx
    exact hinv ⟨mem_map_of_mem H.subtype hx.1, hx.2⟩
  have hselfP : P ⊓ centralizer (P.pCoreIn 2 : Set G) ≤ P.pCoreIn 2 := by
    rw [← map_pCoreIn_of_injective 2 K L.subtype L.subtype_injective]
    exact (inf_centralizer_map_le_iff K (K.pCoreIn 2) L.subtype L.subtype_injective).mpr
      ((inf_centralizer_pCoreIn_le_iff 2 K).mpr hself)
  have hselfF : F ⊓ centralizer (F.pCoreIn 2 : Set H) ≤ F.pCoreIn 2 := by
    apply (inf_centralizer_map_le_iff F (F.pCoreIn 2) H.subtype H.subtype_injective).mp
    rw [map_pCoreIn_of_injective 2 F H.subtype H.subtype_injective, hmF]
    exact hselfP
  have hneK : K.pCoreIn 2 ≠ ⊥ :=
    fun he => hne (((pCore 2 K).map_eq_bot_iff_of_injective K.subtype_injective).mp he)
  have hneP : P.pCoreIn 2 ≠ ⊥ := by
    rw [← map_pCoreIn_of_injective 2 K L.subtype L.subtype_injective]
    exact fun he => hneK (((K.pCoreIn 2).map_eq_bot_iff_of_injective L.subtype_injective).mp he)
  have hneF : F.pCoreIn 2 ≠ ⊥ := by
    intro he
    apply hneP
    have hm := congrArg (Subgroup.map H.subtype) he
    rwa [map_pCoreIn_of_injective 2 F H.subtype H.subtype_injective, hmF, Subgroup.map_bot] at hm
  have hcent := h.component.local_adjoin_centralizer hFL S.isPGroup' hinvH hselfF
  have hcore := h.component.local_adjoin_core_ne_bot hFL hinvH hneF
  have hmX : (F ⊔ (S : Subgroup H)).map H.subtype =
      P ⊔ (S : Subgroup H).map H.subtype := by rw [Subgroup.map_sup, hmF]
  have hmc : ((F ⊔ (S : Subgroup H)).pCoreIn 2).map H.subtype =
      (P ⊔ (S : Subgroup H).map H.subtype).pCoreIn 2 := by
    rw [map_pCoreIn_of_injective 2 _ H.subtype H.subtype_injective, hmX]
  have hcentG := (inf_centralizer_map_le_iff (F ⊔ (S : Subgroup H))
    ((F ⊔ (S : Subgroup H)).pCoreIn 2) H.subtype H.subtype_injective).mpr hcent
  rw [hmX, hmc] at hcentG
  refine ⟨hcentG, ?_, fun _ hx => (le_sup_right :
    (S : Subgroup H).map H.subtype ≤ K.map L.subtype ⊔ (S : Subgroup H).map H.subtype) hx⟩
  intro he
  apply hcore
  apply (((F ⊔ (S : Subgroup H)).pCoreIn 2).map_eq_bot_iff_of_injective H.subtype_injective).mp
  exact hmc.trans he

/-- A block's two-perfection puts it inside the generated local orbit. -/
theorem block_le_local_orbit {H L : Subgroup G} (S : Sylow 2 H) (K : Subgroup L)
    (B : Subgroup (K.map L.subtype ⊔ (S : Subgroup H).map H.subtype : Subgroup G))
    (hB : ChapterC.IsBlock B) :
    B.map (K.map L.subtype ⊔ (S : Subgroup H).map H.subtype).subtype ≤
      componentOrbit (K.map L.subtype) ((S : Subgroup H).map H.subtype) := by
  have hBA := le_local_orbit_of_isPPerfect (K.map L.subtype) _
    (S.isPGroup'.map H.subtype) B hB.short.twoPerfect
  rintro _ ⟨b, hb, rfl⟩
  exact hBA hb

/-- Intersecting an ambient normal two-subgroup with B constructs its layer.
A contained local factor with nonzero third commutator certifies noncentrality. -/
theorem noncentralTwoLayer_of_factor {X : Type*} [Group X]
    (B F Q R : Subgroup X) (hRp : IsPGroup 2 R)
    (hBR : B ≤ normalizer (R : Set X)) (hFB : F ≤ B)
    (hQF : Q ≤ F) (hQR : Q ≤ R) (hthird : ⁅⁅Q, F⁆, Q⁆ ≠ ⊥) :
    HasNoncentralTwoLayer B := by
  refine ⟨B ⊓ R, hRp.to_inf_right, inf_le_left, ?_, ?_⟩
  · exact (le_inf B.le_normalizer hBR).trans inf_normalizer_le_normalizer_inf
  · intro he
    apply hthird
    apply le_bot_iff.mp
    have hQ : Q ≤ B ⊓ R := le_inf (hQF.trans hFB) hQR
    exact he ▸ commutator_mono (commutator_mono hQ hFB) hQ

/-- The orbit of the local two-core lies in the overgroup's actual two-core. -/
theorem local_core_orbit_le {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (K : Subgroup L)
    (hinv : (S : Subgroup H).map H.subtype ⊓ normalizer (L : Set G) ≤
      normalizer (K.map L.subtype : Set G)) :
    componentOrbit ((K.map L.subtype).pCoreIn 2) ((S : Subgroup H).map H.subtype) ≤
      (K.map L.subtype ⊔ (S : Subgroup H).map H.subtype).pCoreIn 2 := by
  let := h.finite
  let P := K.map L.subtype
  let F := P.subgroupOf H
  have hPH : P ≤ H := (map_subtype_le K).trans h.component_le
  have hFL : F ≤ L.subgroupOf H := fun _ hx => map_subtype_le K hx
  have hmF : F.map H.subtype = P := map_subgroupOf_eq_of_le hPH
  have hinvH : (S : Subgroup H) ⊓ normalizer (L.subgroupOf H : Set H) ≤
      normalizer (F : Set H) := by
    rw [← subgroupOf_normalizer_eq h.component_le]
    change (S : Subgroup H) ⊓ (normalizer (L : Set G)).subgroupOf H ≤
      normalizer (P.subgroupOf H : Set H)
    rw [← subgroupOf_normalizer_eq hPH]
    intro x hx
    exact hinv ⟨mem_map_of_mem H.subtype hx.1, hx.2⟩
  have hh := map_mono (f := H.subtype) (h.component.local_core_orbit_le (p := 2) hFL hinvH)
  rw [map_componentOrbit, map_pCoreIn_of_injective 2 F H.subtype H.subtype_injective,
    hmF, map_pCoreIn_of_injective 2 (F ⊔ (S : Subgroup H)) H.subtype H.subtype_injective,
    Subgroup.map_sup, hmF] at hh
  exact hh

private theorem mapped_third_commutator_ne_bot {Y Z : Type*} [Group Y] [Group Z]
    (Q F : Subgroup Y) (f : Y →* Z) (hf : Function.Injective f)
    (hthird : ⁅⁅Q, F⁆, Q⁆ ≠ ⊥) : ⁅⁅Q.map f, F.map f⁆, Q.map f⁆ ≠ ⊥ := by
  intro he
  apply hthird
  apply ((⁅⁅Q, F⁆, Q⁆).map_eq_bot_iff_of_injective hf).mp
  simpa only [map_commutator] using he

/-- A contained conjugate local factor supplies a genuine normal two-layer.
The witness is B ∩ O₂(X). This separates the explicit core and commutator
transfer from the subnormal-product calculation of factor containment. -/
theorem noncentralTwoLayer_of_local_factor {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (K : Subgroup L)
    (hinv : (S : Subgroup H).map H.subtype ⊓ normalizer (L : Set G) ≤
      normalizer (K.map L.subtype : Set G))
    (hthird : ⁅⁅pCore 2 K, (⊤ : Subgroup K)⁆, pCore 2 K⁆ ≠ ⊥)
    (a : (S : Subgroup H).map H.subtype)
    (B : Subgroup (K.map L.subtype ⊔ (S : Subgroup H).map H.subtype : Subgroup G))
    (hfactor : (K.map L.subtype).map (MulAut.conj (a : G)).toMonoidHom ≤
      B.map (K.map L.subtype ⊔ (S : Subgroup H).map H.subtype).subtype) :
    HasNoncentralTwoLayer B := by
  let X := K.map L.subtype ⊔ (S : Subgroup H).map H.subtype
  let P := K.map L.subtype
  let F := P.map (MulAut.conj (a : G)).toMonoidHom
  let Q := (P.pCoreIn 2).map (MulAut.conj (a : G)).toMonoidHom
  have hQF : Q ≤ F := map_mono (pCoreIn_le 2 P)
  have hFX : F ≤ X := hfactor.trans (map_subtype_le B)
  have hQX : Q ≤ X := hQF.trans hFX
  have hQcore : Q ≤ X.pCoreIn 2 :=
    (le_iSup (fun b : (S : Subgroup H).map H.subtype =>
      (P.pCoreIn 2).map (MulAut.conj (b : G)).toMonoidHom) a).trans
        (local_core_orbit_le h K hinv)
  have hthirdL : ⁅⁅K.pCoreIn 2, K⁆, K.pCoreIn 2⁆ ≠ ⊥ := by
    have ht := mapped_third_commutator_ne_bot (pCore 2 K) (⊤ : Subgroup K)
      K.subtype K.subtype_injective hthird
    simpa only [pCoreIn, ← MonoidHom.range_eq_map, K.range_subtype] using ht
  have hthirdG : ⁅⁅P.pCoreIn 2, P⁆, P.pCoreIn 2⁆ ≠ ⊥ := by
    have ht := mapped_third_commutator_ne_bot (K.pCoreIn 2) K
      L.subtype L.subtype_injective hthirdL
    rwa [map_pCoreIn_of_injective 2 K L.subtype L.subtype_injective] at ht
  have hthirdQ : ⁅⁅Q, F⁆, Q⁆ ≠ ⊥ :=
    mapped_third_commutator_ne_bot (P.pCoreIn 2) P
      (MulAut.conj (a : G)).toMonoidHom (MulAut.conj (a : G)).injective hthirdG
  have hFB : F.subgroupOf X ≤ B := by
    intro x hx
    obtain ⟨b, hb, he⟩ := hfactor hx
    exact X.subtype_injective he ▸ hb
  have hQR : Q.subgroupOf X ≤ pCore 2 X := by
    intro x hx
    obtain ⟨q, hq, he⟩ := hQcore hx
    exact X.subtype_injective he ▸ hq
  apply noncentralTwoLayer_of_factor B (F.subgroupOf X) (Q.subgroupOf X) (pCore 2 X)
    pCore_isPGroup le_normalizer_of_normal hFB (subgroupOf_mono X hQF) hQR
  intro he
  apply hthirdQ
  have hm := congrArg (Subgroup.map X.subtype) he
  simpa only [map_commutator, map_subgroupOf_eq_of_le hFX,
    map_subgroupOf_eq_of_le hQX, Subgroup.map_bot] using hm

/-- Transfer local factor containment from H to the common ambient group.
The hypotheses concern relative subnormality in K ⊔ S and intrinsic
perfectness and simplicity of the seed quotient. -/
theorem local_factor_le_of_subnormal {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) [IsSimpleGroup L] (K : Subgroup L)
    (hinv : (S : Subgroup H).map H.subtype ⊓ normalizer (L : Set G) ≤
      normalizer (K.map L.subtype : Set G))
    [Group.IsPerfect K] [IsSimpleGroup (K ⧸ pCore 2 K)]
    (B : Subgroup (K.map L.subtype ⊔ (S : Subgroup H).map H.subtype : Subgroup G))
    (hs : B.IsSubnormal) (hp : IsPPerfect 2 B) (hne : B ≠ ⊥) :
    ∃ a : (S : Subgroup H).map H.subtype,
      (K.map L.subtype).map (MulAut.conj (a : G)).toMonoidHom ≤
        B.map (K.map L.subtype ⊔ (S : Subgroup H).map H.subtype).subtype := by
  let := h.finite
  let P := K.map L.subtype
  let F := P.subgroupOf H
  let XH := F ⊔ (S : Subgroup H)
  let X := P ⊔ (S : Subgroup H).map H.subtype
  have hPH : P ≤ H := (map_subtype_le K).trans h.component_le
  have hFL : F ≤ L.subgroupOf H := fun _ hx => map_subtype_le K hx
  have hmF : F.map H.subtype = P := map_subgroupOf_eq_of_le hPH
  have hinvH : (S : Subgroup H) ⊓ normalizer (L.subgroupOf H : Set H) ≤
      normalizer (F : Set H) := by
    rw [← subgroupOf_normalizer_eq h.component_le]
    change (S : Subgroup H) ⊓ (normalizer (L : Set G)).subgroupOf H ≤
      normalizer (P.subgroupOf H : Set H)
    rw [← subgroupOf_normalizer_eq hPH]
    intro x hx
    exact hinv ⟨mem_map_of_mem H.subtype hx.1, hx.2⟩
  let : IsSimpleGroup (L.subgroupOf H) :=
    (subgroupOfEquivOfLe h.component_le).isSimpleGroup
  let eF : F ≃* K := (subgroupOfEquivOfLe hPH).trans
    (K.equivMapOfInjective L.subtype L.subtype_injective).symm
  let : Group.IsPerfect F := Group.IsPerfect.ofSurjective (f := eF.symm.toMonoidHom)
    eF.symm.surjective
  let : IsSimpleGroup (F ⧸ pCore 2 F) :=
    (QuotientGroup.congr _ _ eF (pCore_map_iso 2 eF)).isSimpleGroup
  have hmX : XH.map H.subtype = X := by rw [Subgroup.map_sup, hmF]
  let eX : XH ≃* X := (XH.equivMapOfInjective H.subtype H.subtype_injective).trans
    (MulEquiv.subgroupCongr hmX)
  have heX (x : XH) : (eX x : G) = (x : H) := rfl
  let C := B.map eX.symm.toMonoidHom
  have hsC : C.IsSubnormal := hs.map eX.symm.surjective
  have hpC : IsPPerfect 2 C := hp.of_surjective (eX.symm.toMonoidHom.subgroupMap B)
    (eX.symm.toMonoidHom.subgroupMap_surjective B)
  have hneC : C ≠ ⊥ := fun hz => hne
    ((B.map_eq_bot_iff_of_injective eX.symm.injective).mp hz)
  obtain ⟨a, ha⟩ := h.component.exists_local_factor_le_of_isSubnormal_isPPerfect
    hFL hinvH S.isPGroup' C hsC hpC hneC
  refine ⟨⟨((a : H) : G), mem_map_of_mem H.subtype a.property⟩, ?_⟩
  rintro x ⟨k, hk, rfl⟩
  have hkF : (⟨k, hPH hk⟩ : H) ∈ F := hk
  obtain ⟨b, hb, hba⟩ := ha (mem_map_of_mem (MulAut.conj (a : H)).toMonoidHom hkF)
  obtain ⟨c, hc, hcb⟩ := hb
  refine ⟨c, hc, ?_⟩
  have hcoe := congrArg (fun y : H => (y : G)) hba
  have he : eX b = c := by
    rw [← hcb]
    exact eX.apply_symm_apply c
  calc
    (c : G) = (eX b : G) := congrArg Subtype.val he.symm
    _ = (b : H) := heX b
    _ = MulAut.conj ((a : H) : G) k := hcoe

/-- Every escaping block has a genuine noncentral normal two-layer.
Only the subnormality and two-perfection clauses of the block definition
are used. The additional source condition B = [B,J(S)] is unnecessary. -/
theorem noncentralTwoLayer_of_local_block {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) [IsSimpleGroup L] (K : Subgroup L)
    (hinv : (S : Subgroup H).map H.subtype ⊓ normalizer (L : Set G) ≤
      normalizer (K.map L.subtype : Set G))
    [Group.IsPerfect K] [IsSimpleGroup (K ⧸ pCore 2 K)]
    (hthird : ⁅⁅pCore 2 K, (⊤ : Subgroup K)⁆, pCore 2 K⁆ ≠ ⊥)
    (B : Subgroup (K.map L.subtype ⊔ (S : Subgroup H).map H.subtype : Subgroup G))
    (hB : ChapterC.IsBlock B)
    (hout : ¬ B.map (K.map L.subtype ⊔ (S : Subgroup H).map H.subtype).subtype ≤ M) :
    HasNoncentralTwoLayer B := by
  have hne : B ≠ ⊥ := by
    intro he
    apply hout
    rw [he, Subgroup.map_bot]
    exact bot_le
  obtain ⟨a, ha⟩ := local_factor_le_of_subnormal h K hinv B hB.subnormal hB.short.twoPerfect hne
  exact noncentralTwoLayer_of_local_factor h K hinv hthird a B ha

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Ree

end
