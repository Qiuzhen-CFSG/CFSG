module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.BinaryG2WeakClosure
public import Theory.GroupTheory.AbelianConjugateSpan
public import Theory.GroupTheory.InvolutionCentralizerControl
public import Theory.Representation.G2NaturalBinary
/-!
# Original unitary fusion from the abelian point closure

The concrete derived binary G₂ action is transitive on nonzero natural
vectors. Transport through the actual induced automizer lifts this to
original component elements. The order-two flag subgroup has the same
normalizer as its generator's centralizer, so the already proved F.9
closure is exactly the closure needed for intersecting-conjugate fusion.
The complete binary fixed-space-family row then gives weak closure.

Source: Aschbacher–Smith 13.3.19(1–2), printed pp.895–896.
-/

public section
open Subgroup CFSG.Quasithin.ChapterE Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
variable {G:Type*} [Group G] [Finite G] {V:Subgroup G} [IsElementaryAbelian 2 V]
omit [Finite G] in
/-- The actual component is transitive on the nonidentity natural module. -/
theorem unitary_component_transitive (L:Subgroup G)
    (e:inducedAutomizer V L≃*Atlas.G2.Natural.BinaryNormalizer.Derived)
    (E:Additive V≃ₗ[ZMod 2]Atlas.G2.Natural.Space (ZMod 2))
    (he:∀(l:inducedAutomizer V L) v,E (automizerRepresentation V l v)=
      Atlas.G2.Natural.derivedAction (ZMod 2) (e l) (E v))
    (z x:G) (hz:z∈V) (hx:x∈V) (hz1:z≠1) (hx1:x≠1) :
    ∃n∈L, n∈normalizer (V:Set G) ∧ MulAut.conj n z=x := by
  let vz:Additive V:=Additive.ofMul ⟨z,hz⟩
  let vx:Additive V:=Additive.ofMul ⟨x,hx⟩
  have hz0:E vz≠0 := by
    intro h
    have hh:E vz=E 0:=h.trans (map_zero E).symm
    exact hz1 (congrArg (fun a:Additive V=>a.toMul.val) (E.injective hh))
  have hx0:E vx≠0 := by
    intro h
    have hh:E vx=E 0:=h.trans (map_zero E).symm
    exact hx1 (congrArg (fun a:Additive V=>a.toMul.val) (E.injective hh))
  obtain ⟨g,hg⟩:=Atlas.G2.Natural.Binary.natural_transitive hz0 hx0
  let i:=e.symm g
  have hi:=he i vz
  rw [e.apply_symm_apply,hg] at hi
  have ha:=E.injective hi
  obtain ⟨n,hn,hnmap⟩:=i.prop
  refine ⟨n.val,hn,n.prop,?_⟩
  have hh:=congrArg (fun a:Additive V=>a.toMul.val) ha
  rw [←hnmap] at hh
  exact hh

omit [Finite G] [IsElementaryAbelian 2 V] in
/-- The literal order-two flag normalizer is its generator centralizer. -/
theorem point_normalizer_eq_generator_centralizer (Z:Subgroup G) (hZ:Nat.card Z=2) (z:G) (hz:z∈Z) (hz1:z≠1) :
    centralizer ({z}:Set G)=normalizer (Z:Set G) := by
  have hgen:zpowers z=Z := by
    have hh:=congrArg (fun A:Subgroup Z=>A.map Z.subtype)
      (zpowers_eq_top_of_prime_card (p:=2) hZ (show (⟨z,hz⟩:Z)≠1 from fun h=>hz1 (congrArg Subtype.val h)))
    simpa only [MonoidHom.map_zpowers,←MonoidHom.range_eq_map,range_subtype,subtype_apply] using hh
  calc
    centralizer ({z}:Set G)=centralizer (Z:Set G) := by
      rw [←centralizer_closure,←zpowers_eq_closure,hgen]
    _=normalizer (Z:Set G):=le_antisymm (Subgroup.centralizer_le_normalizer _)
      (normalizer_le_centralizer_of_card_two Z hZ)

/-- The source abelian point closure gives commutation whenever two
original module conjugates meet nontrivially. -/
theorem unitary_intersecting_conjugates_commute
    (L Z H:Subgroup G) (hZV:Z≤V) (hZ:Nat.card Z=2)
    (hH:H=normalizer (Z:Set G))
    (e:inducedAutomizer V L≃*Atlas.G2.Natural.BinaryNormalizer.Derived)
    (E:Additive V≃ₗ[ZMod 2]Atlas.G2.Natural.Space (ZMod 2))
    (he:∀(l:inducedAutomizer V L) v,E (automizerRepresentation V l v)=
      Atlas.G2.Natural.derivedAction (ZMod 2) (e l) (E v))
    [IsMulCommutative (conjugateSpanBy V H)] (g:G)
    (hinter:V⊓V.map (MulAut.conj g).toMonoidHom≠⊥) :
    ⁅V,V.map (MulAut.conj g).toMonoidHom⁆=⊥ := by
  have hne:Z≠⊥:=Z.one_lt_card_iff_ne_bot.mp (by omega)
  obtain ⟨z,hz1₀⟩:=ne_bot_iff_exists_ne_one.mp hne
  have hz:z.val∈Z:=z.prop
  have hz1:z.val≠1:=fun h=>hz1₀ (Subtype.ext h)
  have hC:centralizer ({(z:G)}:Set G)=H:=
    (point_normalizer_eq_generator_centralizer Z hZ z hz hz1).trans hH.symm
  have hc:centralizerConjugateClosure V z=conjugateSpanBy V H := by
    rw [centralizerConjugateClosure_eq_conjugateSpanBy,hC]
  let :IsMulCommutative (centralizerConjugateClosure V z):=hc.symm ▸ inferInstance
  exact commuting_conjugates_of_transitive_abelian_closure V z g hz1 (by
    intro x hx hx1
    obtain ⟨n,_,hn,heq⟩:=unitary_component_transitive L e E he z x (hZV hz) hx hz1 hx1
    exact ⟨n,hn,heq⟩) hinter

/-- The same original point closure gives W₂(T,V)≤C(V), with transitivity
and the full binary fixed-space-family calculation discharged. -/
theorem unitary_weakClosure_of_point_closure
    (T L Z H:Subgroup G) (hZV:Z≤V) (hZ:Nat.card Z=2)
    (hH:H=normalizer (Z:Set G))
    (hTN:T≤normalizer (V:Set G)) (hLN:L≤normalizer (V:Set G))
    (hNL:normalizer (V:Set G)≤normalizer (L:Set G))
    (e:inducedAutomizer V L≃*Atlas.G2.Natural.BinaryNormalizer.Derived)
    (E:Additive V≃ₗ[ZMod 2]Atlas.G2.Natural.Space (ZMod 2))
    (he:∀(l:inducedAutomizer V L) v,E (automizerRepresentation V l v)=
      Atlas.G2.Natural.derivedAction (ZMod 2) (e l) (E v))
    [IsMulCommutative (conjugateSpanBy V H)] (hr:(3:ℕ∞)<globalR V) :
    indexedWeakClosure V T 2≤centralizer (V:Set G) := by
  let I:=inducedAutomizer V L
  let :(L.subgroupOf (normalizer (V:Set G))).Normal:=
    (normal_subgroupOf_iff_le_normalizer hLN).mpr hNL
  let :I.Normal:=Subgroup.Normal.map inferInstance V.normalizerMonoidHom.rangeRestrict
    V.normalizerMonoidHom.rangeRestrict_surjective
  exact weakClosure_two_of_binaryG2_action hTN
    (fun g=>unitary_intersecting_conjugates_commute L Z H hZV hZ hH e E he g) hr I e E he

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
