module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticSelectionSwap
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticCore
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.DecomposableTwoRank

/-!
# Original quintic action bounds in the exchanging core branch

Cyclicity on each original quintic support identifies every nontrivial
involution restriction with every nontrivial elementary generator of J₁(T).
Its fixed points therefore lie in the original Thompson four-group, and
its displacement lies there as well. These are the source action bounds
needed by the exchanged-support replacement argument.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

private theorem cyclic_restriction_fixed_mono
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (K : Submodule (ZMod 2) W)
    (S : Subgroup D) (hSK : S≤subspaceStabilizer ρ K)
    [IsCyclic (restrictedSubgroup ρ K S)]
    (a : D) (ha : a∈S) (ha2 : a^2=1) (hne : ¬∀v∈K,ρ a v=v)
    (b : D) (hb : b∈S) (hb2 : b^2=1)
    (v : W) (hv : v∈K) (hva : ρ a v=v) : ρ b v=v := by
  let f := subgroupActionHom ρ K S hSK
  let a₀ : S := ⟨a,ha⟩
  let b₀ : S := ⟨b,hb⟩
  have hfa : f a₀≠1 := by
    intro he
    apply hne
    intro w hw
    exact congrArg (fun x => (subspaceImageRepresentation ρ K x ⟨w,hw⟩:W)) he
  by_cases hfb : f b₀=1
  · exact congrArg (fun x => (subspaceImageRepresentation ρ K x ⟨v,hv⟩:W)) hfb
  let ar : restrictedSubgroup ρ K S :=
    ⟨f a₀,(subgroupActionHom_range ρ K S hSK) ▸ ⟨a₀,rfl⟩⟩
  let br : restrictedSubgroup ρ K S :=
    ⟨f b₀,(subgroupActionHom_range ρ K S hSK) ▸ ⟨b₀,rfl⟩⟩
  have hao : orderOf ar=2 := orderOf_eq_prime (Subtype.ext (by
    change f a₀^2=1
    rw [←map_pow,show a₀^2=1 from Subtype.ext ha2,map_one]))
    (fun he => hfa (congrArg Subtype.val he))
  have hbo : orderOf br=2 := orderOf_eq_prime (Subtype.ext (by
    change f b₀^2=1
    rw [←map_pow,show b₀^2=1 from Subtype.ext hb2,map_one]))
    (fun he => hfb (congrArg Subtype.val he))
  have he := congrArg Subtype.val (IsCyclic.eq_of_orderOf_eq_two hbo hao)
  exact (congrArg (fun x => (subspaceImageRepresentation ρ K x ⟨v,hv⟩:W)) he).trans hva

/-- On either original quintic support, an involution preserving the supports
has displacement in the original Thompson four-group. A nontrivial restriction
has no fixed points outside that four-group. -/
theorem DecomposableMarker.ThompsonPair.involution_support_displacement_and_fixed
    {T : Sylow 2 G} {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T:Subgroup G)≤M) (hn : M≤normalizer (V:Set G))
    {U : Submodule (ZMod 2) (Additive V)}
    (c : FactorData (imageRepresentation M V hn) (Jhat (imageRepresentation M V hn)) U)
    (d : Decomposition c.representation) (s : ThompsonPair (T:=T) hn c d)
    (π : internalActionImage M V hn →* Equiv.Perm d.Index)
    (hp : ∀g k,(c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
      (c.ambientFactor d (π g k)).actor)
    (hs : ∀g k,(c.ambientFactor d k).space.map (imageRepresentation M V hn g) =
      (c.ambientFactor d (π g k)).space)
    (hfive : s.prime=5)
    (a : G) (haT : a∈(T:Subgroup G)) (ha : a^2=1)
    (haN : a∈normalizer (plane V (c.ambientFactor d s.first).space : Set G))
    (k : d.Index) :
    let Vi := plane V (c.ambientFactor d k).space
    let Zi := thompsonPlane T V (c.ambientFactor d k).space
    (a∈centralizer (Vi:Set G) ∨ Vi⊓centralizer ({a}:Set G)≤Zi) ∧
      (∀v∈Vi,⁅a,v⁆∈Zi) := by
  let D := internalActionImage M V hn
  let ρ := imageRepresentation M V hn
  let f : M→*D := (actionHom M V hn).rangeRestrict
  let F := c.ambientFactor d k
  let Vi := plane V F.space
  let Zi := thompsonPlane T V F.space
  let J := ChapterB.thompsonJ (T:Subgroup G) 1
  let S : Subgroup D := ((T:Subgroup G).subgroupOf M).map f
  let R := S⊓subspaceStabilizer ρ F.space
  let a₀ : M := ⟨a,hTM haT⟩
  have hJN : J≤normalizer (plane V (c.ambientFactor d s.first).space : Set G) := by
    intro j hj
    apply s.centralizer_le_stabilizer
    refine ⟨ChapterB.thompsonJ_le _ _ hj,?_⟩
    intro z hz
    exact (hz.2.2 j hj).symm
  have hNk (x:G) (hxT:x∈(T:Subgroup G))
      (hxN:x∈normalizer (plane V (c.ambientFactor d s.first).space:Set G)) :
      x∈normalizer (Vi:Set G) := by
    rcases s.covers k with hk | hk
    · simpa only [Vi,F,hk] using hxN
    · simpa only [Vi,F,hk] using s.stabilizes_second ⟨hxT,hxN⟩
  have hstab (x:M) (hx:(x:G)∈normalizer (Vi:Set G)) : f x∈subspaceStabilizer ρ F.space := by
    apply (subspace_map_eq_iff ρ F.space (f x)).mp
    apply plane_injective V
    exact (plane_conjugate hn F.space x).symm.trans (mem_normalizer_iff_map_conj_eq.mp hx)
  have haR : f a₀∈R := ⟨mem_map_of_mem f haT,hstab a₀ (hNk a haT haN)⟩
  have ha2 : (f a₀)^2=1 := by rw [←map_pow,show a₀^2=1 from Subtype.ext ha,map_one]
  have hSp : IsPGroup 2 S :=
    (T.isPGroup'.comap_subtype).map f
  have hm : CyclicSource.DihedralMarking (s.marking k) 5 2 := by simpa only [hfive] using s.dihedral k
  let : IsCyclic (restrictedSubgroup ρ F.space R) := quintic_support_two_cyclic F
    (c.support_stabilizer_normalizes_actor d π hp hs k) (s.marking k)
    (show CyclicSource.DihedralMarking (s.marking k) 5 2 from hm)
    R hSp.to_inf_left inf_le_right
  by_cases hac : a∈centralizer (Vi:Set G)
  · refine ⟨Or.inl hac,?_⟩
    intro v hv
    rw [commutatorElement_eq_one_iff_mul_comm.mpr (hac v hv).symm]
    exact Zi.one_mem
  have hne : ¬∀v∈F.space,ρ (f a₀) v=v := by
    intro hh
    apply hac
    rintro v ⟨w,hw,rfl⟩
    have he := congrArg (fun w:Additive V => (w.toMul:G)) (hh _ hw)
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hfixed : Vi⊓centralizer ({a}:Set G)≤Zi := by
    rintro v ⟨hv,hva⟩
    refine ⟨hv,?_⟩
    have hvV : v∈V := (map_subtype_le _) hv
    refine ⟨hvV,?_⟩
    have hJa : J≤centralizer ({v}:Set G) := by
      apply sSup_le
      intro H hH b hb
      let : IsElementaryAbelian 2 H := hH.2.1
      have hbJ : b∈J := le_sSup hH hb
      have hbT : b∈(T:Subgroup G) := hH.1 hb
      let b₀ : M := ⟨b,hTM hbT⟩
      have hbR : f b₀∈R := ⟨mem_map_of_mem f hbT,hstab b₀ (hNk b hbT (hJN hbJ))⟩
      have hb2 : (f b₀)^2=1 := by
        rw [←map_pow,show b₀^2=1 from Subtype.ext
          (elemPow_eq_one_of_isElementaryAbelian (p:=2) b hb),map_one]
      obtain ⟨w,hw,he⟩ := hv
      have hew : (w:G)=v := he
      have hwfix : ρ (f a₀) (Additive.ofMul w)=Additive.ofMul w := by
        apply Subtype.ext
        change a*(w:G)*a⁻¹=(w:G)
        rw [hew,←mem_centralizer_singleton_iff.mp hva,mul_inv_cancel_right]
      have hbfix := cyclic_restriction_fixed_mono ρ F.space R inf_le_right
        (f a₀) haR ha2 hne (f b₀) hbR hb2 (Additive.ofMul w) hw hwfix
      have hbg := congrArg (fun w:Additive V => (w.toMul:G)) hbfix
      change b*(w:G)*b⁻¹=(w:G) at hbg
      rw [hew] at hbg
      exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hbg)
    intro j hj
    exact mem_centralizer_singleton_iff.mp (hJa hj)
  refine ⟨Or.inr hfixed,?_⟩
  intro v hv
  apply hfixed
  refine ⟨Vi.mul_mem ((mem_normalizer_iff.mp (hNk a haT haN) v).mp hv) (Vi.inv_mem hv),?_⟩
  apply mem_centralizer_singleton_iff.mpr
  have hvV : v∈V := (map_subtype_le _) hv
  have hlin := involution_fixes_displacement ρ
    (show (f a₀)*(f a₀)=1 from by simpa only [pow_two] using ha2)
    (Additive.ofMul (⟨v,hvV⟩:V))
  have hcg := congrArg (fun w:Additive V => (w.toMul:G)) hlin
  change a*((a*v*a⁻¹)/v)*a⁻¹=(a*v*a⁻¹)/v at hcg
  have hh : a*⁅a,v⁆*a⁻¹=⁅a,v⁆ := by
    simpa only [div_eq_mul_inv,commutatorElement_def] using hcg
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

end CFSG.Quasithin.Chapter15.Section01
