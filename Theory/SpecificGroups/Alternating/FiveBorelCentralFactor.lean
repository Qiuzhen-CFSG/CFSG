module

public import Theory.SpecificGroups.Alternating.FiveBorelOvergroups
import all Theory.SpecificGroups.Alternating.FiveExtensionAction
import all Theory.SpecificGroups.Alternating.FiveBorelOvergroups
public import Theory.GroupTheory.PPerfectHom
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# Borel actions and centralizer factors for a normal A₅

The Sylow two-normalizers in A₅ are its self-normalizing A₄ point
stabilizers. For a two-perfect subgroup D containing and normalizing the
embedded Borel B, the sign quotient and the point stabilizer normalizer
force D and B to have the same conjugation image. Consequently the actual
relative centralizer C_{KD}(K) lies in D.

An odd permutation normalizing this A₄ has a nontrivial cubic commutator
with an explicit three-cycle. This commutator cannot lie in its two-core.
Transporting cores and commutators along the genuine conjugation map then
shows that an actor centralizing Y/O₂(Y), where Y has the Borel's action
image, acts on K by an inner automorphism.

The internal imports of the two five-point companion modules reuse the
proved point-stabilizer normalizer calculation and supply the defining
equation of the existing action, both published below. They leave the
upstream definitions and public boundaries unchanged.

Source application: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 13.8.20, printed pp.954–955 (PDF pp.971–972).
-/

public section
open Subgroup
open scoped commutatorElement
namespace Theory.SpecificGroups.Alternating.FiveBorelCentralFactor
local notation "S5" => Equiv.Perm (Fin 5)
local notation "A5" => alternatingGroup (Fin 5)

/-- The normalizer in S₅ of an even point stabilizer fixes that same point. -/
theorem even_stabilizer_normalizer (i : Fin 5) :
    normalizer ((A5 ⊓ MulAction.stabilizer S5 i : Subgroup S5) : Set S5) =
      MulAction.stabilizer S5 i := by
  exact FiveBorelOvergroups.evenStabilizer_normalizer i

/-- The A₄ Borel is self-normalizing inside A₅. -/
theorem even_stabilizer_self_normalizing (i : Fin 5) :
    normalizer (MulAction.stabilizer A5 i : Set A5) = MulAction.stabilizer A5 i := by
  apply le_antisymm _ le_normalizer
  intro g hg
  have hm : (MulAction.stabilizer A5 i).map (A5).subtype =
      A5 ⊓ MulAction.stabilizer S5 i := by
    ext x
    exact ⟨fun ⟨y, hy, he⟩ => he ▸ ⟨y.property, hy⟩,
      fun ⟨ha, hi⟩ => ⟨⟨x, ha⟩, hi, rfl⟩⟩
  have h := le_normalizer_map (A5).subtype (mem_map.mpr ⟨g, hg, rfl⟩)
  rw [hm, even_stabilizer_normalizer] at h
  exact h

/-- An odd point-fixing permutation moves the cubic quotient: the commutator
with a specified three-cycle has nontrivial order three. -/
theorem odd_actor_cubic_witness (i : Fin 5) (t : S5)
    (hti : t i = i) (htodd : t.sign ≠ 1) :
    ∃ b ∈ A5 ⊓ MulAction.stabilizer S5 i, ⁅b, t⁆ ^ 3 = 1 ∧ ⁅b, t⁆ ≠ 1 := by
  let b (j : Fin 5) : S5 :=
    Equiv.swap 4 j * (Equiv.swap 0 1 * Equiv.swap 1 2) * Equiv.swap 4 j
  have hb : ∀ j, (b j).sign = 1 ∧ b j j = j := by decide +kernel
  have hc : ∀ (j : Fin 5) (s : S5), s j = j → s.sign ≠ 1 →
      ⁅b j, s⁆ ^ 3 = 1 ∧ ⁅b j, s⁆ ≠ 1 := by decide +kernel
  exact ⟨b i, ⟨Equiv.Perm.mem_alternatingGroup.mpr (hb i).1, (hb i).2⟩,
    hc i t hti htodd⟩


variable {G : Type*} [Group G]

/-- The five-point action is the genuine conjugation map, transported by
Aut(A₅) ≃ S₅ and the prescribed identification of K. -/
theorem action_eq_conjugation (K : Subgroup G) [K.Normal] (eK : K ≃* A5) :
    FiveExtensionAction.action K eK =
      ((MulAut.congr eK).trans FiveExtensionAction.symmetricAutEquiv.symm).toMonoidHom.comp
        (MulAut.conjNormal : G →* MulAut K) := by rfl

/-- The actual ambient image of the Sylow normalizer in K. -/
@[expose] def borel (K : Subgroup G) (P : Sylow 2 K) : Subgroup G :=
  (normalizer (P : Set K)).map K.subtype

/-- Five-point coordinates for this particular embedded Borel. -/
theorem borel_action (K : Subgroup G) [K.Normal]
    (eK : K ≃* A5) (P : Sylow 2 K) :
    ∃ i : Fin 5, (borel K P).map (FiveExtensionAction.action K eK) =
      A5 ⊓ MulAction.stabilizer S5 i := by
  let : Finite K := Finite.of_equiv A5 eK.symm.toEquiv
  let P' := P.mapSurjective (f := eK.toMonoidHom) eK.surjective
  obtain ⟨i, hi⟩ := FiveBorelOvergroups.sylow_normalizer_eq_stabilizer P'
  have hhom : (FiveExtensionAction.action K eK).comp K.subtype =
      (A5).subtype.comp eK.toMonoidHom := by
    apply MonoidHom.ext
    exact FiveExtensionAction.action_on_subgroup K eK
  refine ⟨i, ?_⟩
  rw [borel, map_map, hhom, ← map_map]
  change ((normalizer ((P : Subgroup K) : Set K)).map eK.toMonoidHom).map _ = _
  rw [map_equiv_normalizer_eq]
  change (normalizer (P' : Set A5)).map (A5).subtype = _
  rw [hi]
  ext x
  exact ⟨fun ⟨y, hy, he⟩ => he ▸ ⟨y.property, hy⟩,
    fun ⟨ha, hi⟩ => ⟨⟨x, ha⟩, hi, rfl⟩⟩

/-- Every actual A₅ Sylow normalizer is self-normalizing. -/
theorem sylow_normalizer_self_normalizing
    {J : Type*} [Group J] (eJ : J ≃* A5) (P : Sylow 2 J) :
    normalizer (normalizer (P : Set J) : Set J) = normalizer (P : Set J) := by
  let : Finite J := Finite.of_equiv A5 eJ.symm.toEquiv
  let P' := P.mapSurjective (f := eJ.toMonoidHom) eJ.surjective
  obtain ⟨i, hi⟩ := FiveBorelOvergroups.sylow_normalizer_eq_stabilizer P'
  have hm : (normalizer (P : Set J)).map eJ.toMonoidHom = MulAction.stabilizer A5 i := by
    change (normalizer ((P : Subgroup J) : Set J)).map eJ.toMonoidHom = _
    rw [map_equiv_normalizer_eq]
    exact hi
  apply map_injective (f := eJ.toMonoidHom) eJ.injective
  rw [map_equiv_normalizer_eq, hm, even_stabilizer_self_normalizing]

private theorem twoPerfect_action_even (K D : Subgroup G) [K.Normal]
    (eK : K ≃* A5) (hD : IsPPerfect 2 D) :
    D.map (FiveExtensionAction.action K eK) ≤ A5 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htwo : IsPGroup 2 (S5 ⧸ A5) := by
    apply IsPGroup.of_card (n := 1)
    rw [← (A5).index_eq_card, alternatingGroup.index_eq_two]
    rfl
  let f : D →* S5 ⧸ A5 := (QuotientGroup.mk' A5).comp
    ((FiveExtensionAction.action K eK).comp D.subtype)
  have hf := hD.hom_eq_one_of_isPGroup htwo f
  rintro x ⟨d, hd, rfl⟩
  exact (QuotientGroup.eq_one_iff _).mp
    (congrArg (fun z : D →* S5 ⧸ A5 => z ⟨d, hd⟩) hf)

/-- A two-perfect normalizing overgroup has exactly the Borel's five-point image. -/
theorem twoPerfect_action_eq_borel (K D : Subgroup G) [K.Normal]
    (eK : K ≃* A5) (P : Sylow 2 K) (hD : IsPPerfect 2 D)
    (hBD : borel K P ≤ D) (hDN : D ≤ normalizer (borel K P : Set G)) :
    D.map (FiveExtensionAction.action K eK) =
      (borel K P).map (FiveExtensionAction.action K eK) := by
  obtain ⟨i, hi⟩ := borel_action K eK P
  apply le_antisymm _ (map_mono hBD)
  rw [hi]
  refine le_inf (twoPerfect_action_even K D eK hD) ?_
  have hn := (map_mono (f := FiveExtensionAction.action K eK) hDN).trans
    (le_normalizer_map (FiveExtensionAction.action K eK))
  rwa [hi, even_stabilizer_normalizer] at hn

/-- Equality of images in the actual automorphism group of K. -/
theorem twoPerfect_conjugation_eq_borel (K D : Subgroup G) [K.Normal]
    (eK : K ≃* A5) (P : Sylow 2 K) (hD : IsPPerfect 2 D)
    (hBD : borel K P ≤ D) (hDN : D ≤ normalizer (borel K P : Set G)) :
    D.map (MulAut.conjNormal : G →* MulAut K) =
      (borel K P).map (MulAut.conjNormal : G →* MulAut K) := by
  let e := (MulAut.congr eK).trans FiveExtensionAction.symmetricAutEquiv.symm
  apply map_injective (f := e.toMonoidHom) e.injective
  rw [map_map, map_map]
  exact twoPerfect_action_eq_borel K D eK P hD hBD hDN

/-- The relative centralizer in KD lies in D; no product inside D is assumed. -/
theorem centralizer_le_twoPerfect (K D : Subgroup G) [K.Normal]
    (eK : K ≃* A5) (P : Sylow 2 K) (hD : IsPPerfect 2 D)
    (hBD : borel K P ≤ D) (hDN : D ≤ normalizer (borel K P : Set G)) :
    (K ⊔ D) ⊓ centralizer (K : Set G) ≤ D := by
  let f := FiveExtensionAction.action K eK
  have heq := twoPerfect_action_eq_borel K D eK P hD hBD hDN
  rintro x ⟨hx, hc⟩
  obtain ⟨k, hk, d, hd, rfl⟩ := mem_sup_of_normal_left.mp hx
  have hfx : f (k * d) = 1 := by
    have hconj : (MulAut.conjNormal (k * d) : MulAut K) = 1 := by
      change k * d ∈ (MulAut.conjNormal : G →* MulAut K).ker
      rwa [MulAut.conjNormal_ker_eq_centralizer]
    change FiveExtensionAction.symmetricAutEquiv.symm ((MulAut.congr eK) _) = 1
    rw [hconj, map_one, map_one]
  have hdm : f d ∈ (borel K P).map f := heq ▸ mem_map.mpr ⟨d, hd, rfl⟩
  obtain ⟨b, hb, hbf⟩ := hdm
  have hbK : b ∈ K := (map_subtype_le _) hb
  have hkb : k * b = 1 := by
    have h : f (k * b) = 1 := by rw [map_mul, hbf, ← map_mul]; exact hfx
    have h' : (eK ⟨k * b, K.mul_mem hk hbK⟩).val = 1 :=
      (FiveExtensionAction.action_on_subgroup K eK ⟨k * b, K.mul_mem hk hbK⟩).symm.trans h
    have h'' : eK ⟨k * b, K.mul_mem hk hbK⟩ = 1 := Subtype.ext h'
    exact congrArg Subtype.val (eK.injective (h''.trans eK.map_one.symm))
  have hkD : k ∈ D := by
    have : k = b⁻¹ := eq_inv_of_mul_eq_one_left hkb
    rw [this]
    exact D.inv_mem (hBD hb)
  exact D.mul_mem hkD hd


/-- The image of the embedded two-core lies in the embedded core of the image.
No assertion about the kernel of f, or ambient normality of Y, is needed. -/
theorem core_image_le {J : Type*} [Group J] (f : G →* J) (Y : Subgroup G) :
    (Y.pCoreIn 2).map f ≤ (Y.map f).pCoreIn 2 := by
  let g := f.subgroupMap Y
  have hn : ((pCore 2 Y).map g).Normal :=
    Subgroup.Normal.map inferInstance g (f.subgroupMap_surjective Y)
  have hcore : (pCore 2 Y).map g ≤ pCore 2 (Y.map f) :=
    le_sSup ⟨hn, pCore_isPGroup.map g⟩
  have h := map_mono (f := (Y.map f).subtype) hcore
  have hg : (Y.map f).subtype.comp g = f.comp Y.subtype := by
    ext y
    rfl
  simpa only [pCoreIn, map_map, hg] using h

/-- Restricting to a containing ambient subgroup preserves the embedded core. -/
theorem core_subgroupOf_map {Y H : Subgroup G} (hYH : Y ≤ H) :
    ((Y.subgroupOf H).pCoreIn 2).map H.subtype = Y.pCoreIn 2 := by
  let e := subgroupOfEquivOfLe hYH
  calc
    _ = ((pCore 2 (Y.subgroupOf H)).map e.toMonoidHom).map Y.subtype := by
      rw [pCoreIn, map_map, map_map]
      rfl
    _ = _ := by rw [pCore_map_iso]; rfl

/-- Transport the commutator bound through an arbitrary actual homomorphism. -/
theorem commutator_image_le_core {J : Type*} [Group J] (f : G →* J)
    (Y : Subgroup G) (t : G) (h : ⁅Y, zpowers t⁆ ≤ Y.pCoreIn 2) :
    ⁅Y.map f, zpowers (f t)⁆ ≤ (Y.map f).pCoreIn 2 := by
  have hm := (map_mono (f := f) h).trans (core_image_le f Y)
  rwa [map_commutator, MonoidHom.map_zpowers] at hm

/-- An odd permutation fixing the Borel point acts nontrivially modulo its
actual two-core: its cubic commutator survives that quotient. -/
theorem odd_actor_moves_core_quotient (i : Fin 5) (t : S5)
    (hti : t i = i) (htodd : t.sign ≠ 1) :
    ¬ ⁅A5 ⊓ MulAction.stabilizer S5 i, zpowers t⁆ ≤
      (A5 ⊓ MulAction.stabilizer S5 i).pCoreIn 2 := by
  intro h
  obtain ⟨b, hb, hcube, hne⟩ := odd_actor_cubic_witness i t hti htodd
  have hc := h (commutator_mem_commutator hb (mem_zpowers t))
  let c : (A5 ⊓ MulAction.stabilizer S5 i).pCoreIn 2 := ⟨⁅b, t⁆, hc⟩
  have hpow : c ^ 3 = 1 := Subtype.ext hcube
  have hcop := (isPGroup_pCoreIn 2 (A5 ⊓ MulAction.stabilizer S5 i)).orderOf_coprime
    (by decide : Nat.Coprime 2 3) c
  have hc1 : c = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes hcop dvd_rfl (orderOf_dvd_of_pow_eq_one hpow))
  exact hne (congrArg Subtype.val hc1)

/-- A Borel-normalizing actor centralizing the cubic quotient of a subgroup
with the Borel's action on K induces an inner automorphism of K. -/
theorem inner_of_borel_image_commutator (K Y : Subgroup G) [K.Normal]
    (eK : K ≃* A5) (P : Sylow 2 K) (t : G)
    (himage : Y.map (MulAut.conjNormal : G →* MulAut K) =
      (borel K P).map (MulAut.conjNormal : G →* MulAut K))
    (ht : t ∈ normalizer (borel K P : Set G))
    (hcomm : ⁅Y, zpowers t⁆ ≤ Y.pCoreIn 2) :
    (MulAut.conjNormal t : MulAut K) ∈ MulAut.innerSubgroup K := by
  let f := FiveExtensionAction.action K eK
  let e := (MulAut.congr eK).trans FiveExtensionAction.symmetricAutEquiv.symm
  have himage' : Y.map f = (borel K P).map f := by
    have hm := congrArg (Subgroup.map e.toMonoidHom) himage
    change Y.map (e.toMonoidHom.comp MulAut.conjNormal) =
      (borel K P).map (e.toMonoidHom.comp MulAut.conjNormal)
    simpa only [map_map] using hm
  obtain ⟨i, hi⟩ := borel_action K eK P
  have hti : f t i = i := by
    have hn := le_normalizer_map f (mem_map.mpr ⟨t, ht, rfl⟩)
    rw [hi, even_stabilizer_normalizer] at hn
    exact hn
  have hcomm' := commutator_image_le_core f Y t hcomm
  rw [himage', hi] at hcomm'
  have hsign : (f t).sign = 1 := by
    by_contra hodd
    exact odd_actor_moves_core_quotient i (f t) hti hodd hcomm'
  let k : K := eK.symm ⟨f t, Equiv.Perm.mem_alternatingGroup.mpr hsign⟩
  have hkt : f k.val = f t :=
    (FiveExtensionAction.action_on_subgroup K eK k).trans
      (congrArg Subtype.val (eK.apply_symm_apply _))
  refine ⟨k, ?_⟩
  apply e.injective
  change e (MulAut.conjNormal k.val) = e (MulAut.conjNormal t) at hkt
  simpa only [MulAut.conjNormal_val] using hkt

end Theory.SpecificGroups.Alternating.FiveBorelCentralFactor
