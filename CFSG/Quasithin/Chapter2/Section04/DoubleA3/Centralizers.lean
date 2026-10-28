module
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.PairCoordinates

/-!
# The original paired-cubic involution centralizers

The two fixed involutions are exchanged by the original block conjugator,
while x fixes both. The index-four Thompson subgroup therefore has index two
in each Sylow centralizer. Each opposite cubic block escapes M and centralizes
the corresponding involution; the original characteristic-two local subgroup
then puts the full centralizer in Γ. Its two-part attains the existing maximal
bound, proving both Γ maximality and the literal Sylow assertion. The two
Sylow images coincide with R⟨x⟩ inside the original ambient T.

Source: Aschbacher–Smith, paragraph following 2.4.30, printed p.547.
-/

@[expose] public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter2.DoubleA3
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

private theorem index_four_intermediate (R N T : Subgroup G)
    (hRN : R ≤ N) (hNT : N ≤ T) (hi : R.relIndex T = 4)
    (x s : G) (hx : x ∈ N) (hxR : x ∉ R) (hs : s ∈ T) (hsN : s ∉ N) :
    R.relIndex N = 2 ∧ N.relIndex T = 2 := by
  have ha : 2 ≤ R.relIndex N := by
    have hp : 0 < R.relIndex N := Nat.pos_of_ne_zero index_ne_zero_of_finite
    have hn : R.relIndex N ≠ 1 := fun he => hxR (relIndex_eq_one.mp he hx)
    omega
  have hb : 2 ≤ N.relIndex T := by
    have hp : 0 < N.relIndex T := Nat.pos_of_ne_zero index_ne_zero_of_finite
    have hn : N.relIndex T ≠ 1 := fun he => hsN (relIndex_eq_one.mp he hs)
    omega
  have hm := relIndex_mul_relIndex R N T hRN hNT
  rw [hi] at hm
  constructor <;> nlinarith

private theorem index_two_generated (R N : Subgroup G) (hRN : R ≤ N)
    (hi : R.relIndex N = 2) (x : G) (hx : x ∈ N) (hxR : x ∉ R) :
    N = R ⊔ zpowers x := by
  let P := R ⊔ zpowers x
  have hPN : P ≤ N := sup_le hRN (zpowers_le.mpr hx)
  have hiRP : 2 ≤ R.relIndex P := by
    have hp : 0 < R.relIndex P := Nat.pos_of_ne_zero index_ne_zero_of_finite
    have hn : R.relIndex P ≠ 1 := fun he => hxR (relIndex_eq_one.mp he (mem_sup_right (mem_zpowers x)))
    omega
  have hm := relIndex_mul_relIndex R P N le_sup_left hPN
  rw [hi] at hm
  have hp : 0 < P.relIndex N := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hPNi : P.relIndex N = 1 := by nlinarith
  exact le_antisymm (relIndex_eq_one.mp hPNi) hPN

private theorem centralizer_mem_gamma (d : MinimalBlockSetup M)
    (R : Subgroup G) (hR : R ∈ beta M) (hRH : R ≤ d.H)
    (z : G) (hz : orderOf z = 2) (hzH : z ∈ d.H)
    (hzR : z ∈ centralizer (R : Set G))
    (L : Subgroup G) (hLH : L ≤ d.H) (hout : ¬ L ≤ M)
    (hLC : L ≤ centralizer ({z} : Set G)) :
    centralizer ({z} : Set G) ∈ gamma (Chapter1.He G) M := by
  let W := zpowers z
  let N := centralizer ({z} : Set G)
  have hWcard : Nat.card W = 2 := by rw [Nat.card_zpowers,hz]
  have hWp : IsPGroup 2 W := IsPGroup.of_card (n := 1) (by simpa using hWcard)
  have hWne : W ≠ ⊥ := by intro he; rw [he,card_bot] at hWcard; omega
  have hWH : W ≤ d.H := zpowers_le.mpr hzH
  have hC : centralizer (W : Set G) = N := by
    rw [show W = zpowers z from rfl,zpowers_eq_closure,centralizer_closure]
  have hN : normalizer (W : Set G) = N :=
    le_antisymm ((normalizer_le_centralizer_of_card_two W hWcard).trans hC.le)
      (hC.symm ▸ Subgroup.centralizer_le_normalizer _)
  have hWN : W ≤ N := hN ▸ W.le_normalizer
  have hJe : d.H ⊓ N ∈ Chapter1.He G := by
    rw [←hN]
    exact Chapter1.normalizer_mem_He_of_isPGroup d.mem_gammaEvenZero.2 hWp hWH
  have hWJ : W ≤ d.H ⊓ N := le_inf hWH hWN
  have hQJ : W ≤ twoCore (d.H ⊓ N) := le_pCoreIn_of_normalizes hWp hWJ (hN.symm ▸ inf_le_right)
  have hQN : W ≤ twoCore N := le_pCoreIn_of_normalizes hWp hWN hN.ge
  have hRN : R ≤ N := by
    intro r hr
    exact mem_centralizer_singleton_iff.mpr (hzR r hr)
  have hJout : ¬ d.H ⊓ N ≤ M := fun hle => hout ((le_inf hLH hLC).trans hle)
  exact ⟨fun he => hWne (bot_unique (he ▸ hQN)), (R,d.H ⊓ N),
    ⟨hR,hJe,fun he => hWne (bot_unique (he ▸ hQJ)),le_inf hRH hRN,hJout⟩,
    inf_le_right⟩

private theorem centralizer_sylow_geometry (d : MinimalBlockSetup M) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype ≤ (T : Subgroup G))
    (hRS : sourceR d ≤ (d.S : Subgroup d.H).map d.H.subtype)
    (hR : sourceR d ∈ beta M)
    (hHmax : d.H ∈ gammaMax (Chapter1.He G) M)
    (hiST : ((d.S : Subgroup d.H).map d.H.subtype).relIndex (T : Subgroup G) = 2)
    (hiRT : (sourceR d).relIndex (T : Subgroup G) = 4)
    (z x s : G) (hz : z ∈ centralizer (sourceR d : Set G))
    (hgamma : centralizer ({z} : Set G) ∈ gamma (Chapter1.He G) M)
    (hxT : x ∈ (T : Subgroup G)) (hxC : x ∈ centralizer ({z} : Set G))
    (hxS : x ∉ (d.S : Subgroup d.H).map d.H.subtype)
    (hsT : s ∈ (T : Subgroup G)) (hsC : s ∉ centralizer ({z} : Set G)) :
    centralizer ({z} : Set G) ∈ gammaMax (Chapter1.He G) M ∧
      ∃ P : Sylow 2 (centralizer ({z} : Set G)),
        (P : Subgroup _).map (centralizer ({z} : Set G)).subtype =
          (T : Subgroup G) ⊓ centralizer ({z} : Set G) ∧
        (P : Subgroup _).map (centralizer ({z} : Set G)).subtype = sourceR d ⊔ zpowers x ∧
        (sourceR d).relIndex ((P : Subgroup _).map (centralizer ({z} : Set G)).subtype) = 2 ∧
        ((P : Subgroup _).map (centralizer ({z} : Set G)).subtype).relIndex (T : Subgroup G) = 2 := by
  let C := centralizer ({z} : Set G)
  let N := (T : Subgroup G) ⊓ C
  have hRN : sourceR d ≤ N := le_inf (hRS.trans hST) (by
    intro r hr
    exact mem_centralizer_singleton_iff.mpr (hz r hr))
  have hxR : x ∉ sourceR d := fun hh => hxS (hRS hh)
  have hi := index_four_intermediate (sourceR d) N T hRN inf_le_left hiRT
    x s ⟨hxT,hxC⟩ hxR hsT (fun hh => hsC hh.2)
  have hNcard : Nat.card N = Nat.card ((d.S : Subgroup d.H).map d.H.subtype) := by
    have hn := relIndex_mul_relIndex (⊥ : Subgroup G) N (T : Subgroup G) bot_le inf_le_left
    have hs := relIndex_mul_relIndex (⊥ : Subgroup G) ((d.S : Subgroup d.H).map d.H.subtype)
      (T : Subgroup G) bot_le hST
    rw [relIndex_bot_left,relIndex_bot_left,hi.2] at hn
    rw [relIndex_bot_left,relIndex_bot_left,hiST] at hs
    omega
  have hNb : N ∈ beta M := beta_mono hR hRN (T.isPGroup'.to_le inf_le_left)
  have hmax := gammaMax_of_twoPart_le hHmax hgamma (by
    rw [←sylow_image_card d.H d.S,←hNcard]
    exact beta_card_le_twoPart hNb inf_le_right)
  have hc : Nat.card N = twoPart C := hNcard.trans ((sylow_image_card d.H d.S).trans hmax.2.symm)
  obtain ⟨P,hP⟩ := exists_sylow_of_card (show N ≤ C from inf_le_right) hc
  refine ⟨hmax.1,P,hP,hP.trans ?_,hP.symm ▸ hi.1,hP.symm ▸ hi.2⟩
  exact index_two_generated (sourceR d) N hRN hi.1 x ⟨hxT,hxC⟩ hxR

open ChapterC.Section05.BlockAnalysis ChapterC.Section05.ConjugateSource
/-- The two literal involution centralizers selected after source 2.4.30. -/
structure SourceCentralizerGeometry {d : MinimalBlockSetup M} {T : Sylow 2 G}
    (c : SourcePairCoordinates d T) where
  z₁ : G
  z₂ : G
  order_first : orderOf z₁ = 2
  order_second : orderOf z₂ = 2
  distinct : z₁ ≠ z₂
  first_mem : z₁ ∈ c.U₁
  second_mem : z₂ ∈ c.U₂
  first_fixed : z₁ ∈ centralizer (sourceR d : Set G)
  second_fixed : z₂ ∈ centralizer (sourceR d : Set G)
  exchange : c.s * z₁ * c.s⁻¹ = z₂
  x_first : c.x ∈ centralizer ({z₁} : Set G)
  x_second : c.x ∈ centralizer ({z₂} : Set G)
  first_max : centralizer ({z₁} : Set G) ∈ gammaMax (Chapter1.He G) M
  second_max : centralizer ({z₂} : Set G) ∈ gammaMax (Chapter1.He G) M
  P₁ : Sylow 2 (centralizer ({z₁} : Set G))
  P₂ : Sylow 2 (centralizer ({z₂} : Set G))
  first_intersection : (P₁ : Subgroup _).map (centralizer ({z₁} : Set G)).subtype =
    (T : Subgroup G) ⊓ centralizer ({z₁} : Set G)
  second_intersection : (P₂ : Subgroup _).map (centralizer ({z₂} : Set G)).subtype =
    (T : Subgroup G) ⊓ centralizer ({z₂} : Set G)
  first_span : (P₁ : Subgroup _).map (centralizer ({z₁} : Set G)).subtype = sourceR d ⊔ zpowers c.x
  second_span : (P₂ : Subgroup _).map (centralizer ({z₂} : Set G)).subtype = sourceR d ⊔ zpowers c.x
  first_index : (sourceR d).relIndex ((P₁ : Subgroup _).map (centralizer ({z₁} : Set G)).subtype) = 2
  second_index : (sourceR d).relIndex ((P₂ : Subgroup _).map (centralizer ({z₂} : Set G)).subtype) = 2
  first_sylow_index : ((P₁ : Subgroup _).map (centralizer ({z₁} : Set G)).subtype).relIndex (T : Subgroup G) = 2
  second_sylow_index : ((P₂ : Subgroup _).map (centralizer ({z₂} : Set G)).subtype).relIndex (T : Subgroup G) = 2

 theorem SourcePairCoordinates.exists_centralizer_geometry
    {d : MinimalBlockSetup M} {T : Sylow 2 G} (c : SourcePairCoordinates d T)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (hM : IsMaximalTwoLocal M)
    (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hpair : d.L0 ≠ d.block) : Nonempty (SourceCentralizerGeometry c) := by
  have hg := d.paired_cubic_source_sylow_geometry hG T hM hTM hu hST hpair c.cubic_first
  have hRS : sourceR d ≤ (d.S : Subgroup d.H).map d.H.subtype := sSup_le (fun _ h => h.1)
  have hRH : sourceR d ≤ d.H := hRS.trans (map_subtype_le _)
  have hU₁R : c.U₁ ≤ sourceR d := c.baumann ▸ c.first.module_le
  have hU₂R : c.U₂ ≤ sourceR d := c.baumann ▸ c.second.module_le
  obtain ⟨z₁,z₂,hz₁,hz₂,hne,hz₁U,hz₂U,hz₁R,hz₂R,hex,hx₁,hx₂⟩ := c.exists_fixed_involutions
  have hs₁ : c.s ∉ centralizer ({z₁} : Set G) := by
    intro hs
    have hh : c.s * z₁ * c.s⁻¹ = z₁ := by rw [mem_centralizer_singleton_iff.mp hs,mul_inv_cancel_right]
    exact hne (hh.symm.trans hex)
  have hs₂ : c.s ∉ centralizer ({z₂} : Set G) := by
    intro hs
    apply hne
    apply (MulAut.conj c.s).injective
    change c.s * z₁ * c.s⁻¹ = c.s * z₂ * c.s⁻¹
    rw [hex,mem_centralizer_singleton_iff.mp hs,mul_inv_cancel_right]
  have hLK : c.L ≤ d.H := (le_sup_right.trans c.residual.ge).trans (map_subtype_le _)
  have hLout : ¬ c.L ≤ M := by
    intro hLM
    have hsM : c.s ∈ M := hTM (hST.le c.s_mem)
    apply d.outside
    intro k hk
    have hkL : c.s*k*c.s⁻¹ ∈ c.L := c.exchange ▸ mem_map_of_mem (MulAut.conj c.s).toMonoidHom hk
    have hh := M.mul_mem (M.mul_mem (M.inv_mem hsM) (hLM hkL)) hsM
    simpa only [mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one] using hh
  have hLC : c.L ≤ centralizer ({z₁} : Set G) := by
    intro l hl
    exact mem_centralizer_singleton_iff.mpr (c.commute hl z₁ ((map_subtype_le _) hz₁U)).symm
  have hKC : d.block.map d.H.subtype ≤ centralizer ({z₂} : Set G) := by
    intro k hk
    exact mem_centralizer_singleton_iff.mpr
      (le_centralizer_iff.mp c.commute hk z₂ ((map_subtype_le _) hz₂U)).symm
  have hγ₁ := centralizer_mem_gamma d (sourceR d) hg.2.2.2.2.2.1 hRH z₁ hz₁
    (hRH (hU₁R hz₁U)) hz₁R c.L hLK hLout hLC
  have hγ₂ := centralizer_mem_gamma d (sourceR d) hg.2.2.2.2.2.1 hRH z₂ hz₂
    (hRH (hU₂R hz₂U)) hz₂R (d.block.map d.H.subtype) (map_subtype_le _) d.outside hKC
  have hf₁ := centralizer_sylow_geometry d T hST.le hRS hg.2.2.2.2.2.1 hg.2.2.2.2.2.2.1
    c.index hg.2.2.1 z₁ c.x c.s hz₁R hγ₁ c.x_mem hx₁ c.x_outside (hST.le c.s_mem) hs₁
  have hf₂ := centralizer_sylow_geometry d T hST.le hRS hg.2.2.2.2.2.1 hg.2.2.2.2.2.2.1
    c.index hg.2.2.1 z₂ c.x c.s hz₂R hγ₂ c.x_mem hx₂ c.x_outside (hST.le c.s_mem) hs₂
  obtain ⟨hm₁,P₁,hP₁,hspan₁,hi₁,hTi₁⟩ := hf₁
  obtain ⟨hm₂,P₂,hP₂,hspan₂,hi₂,hTi₂⟩ := hf₂
  exact ⟨⟨z₁,z₂,hz₁,hz₂,hne,hz₁U,hz₂U,hz₁R,hz₂R,hex,hx₁,hx₂,hm₁,hm₂,
    P₁,P₂,hP₁,hP₂,hspan₁,hspan₂,hi₁,hi₂,hTi₁,hTi₂⟩⟩

end CFSG.Quasithin.Chapter2.DoubleA3
