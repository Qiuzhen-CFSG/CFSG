module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.EvenLocalCandidates.SylowCatalogue.Enumeration
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.EvenLocalCandidates.SylowCatalogue.Small

/-!
# Excluding all other elements from normal elementary subgroups

An element of a normal elementary abelian subgroup squares to one and
commutes with its conjugates. For every enumerated word outside the eight
specified products, a point witnesses failure of one of these conditions.
This proves the needed containment without classifying all normal subgroups.

Source: the concrete ATLAS subgroup for GLS volume 3, Table 5.3m, printed p.274.
The witnesses are reproduced by `source/generate.py`; each is checked in Lean.
-/

@[expose] public section
namespace Sporadic.LeechRelated.HS.EvenLocalCandidates.SylowCatalogueData
open Subgroup Theory.GroupTheory
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
set_option Elab.async false

private def smallRow : Fin 8 → Fin 512 := ![0, 10, 480, 494, 32, 128, 303, 143]
private def smallCode (i : Fin 512) : Fin 8 :=
  ⟨(401397652936241403017275701891930822554634878987465356180180134670705513114868052661353979634390045248440563826047326762769241101858264271749113788474141550873354614972575310673374177918988102074939096666110852271166610864341652944784760002119283701735434975236838659033606075579803998781176656755316765572863816761556406288692024600812930977085741609172059161387300035971589882504650988248564358422230524041362248645880217504911683802031212986368 >>> (3 * i.val)) % 8, Nat.mod_lt _ (by decide)⟩
private def badPoint (i : Fin 512) : Fin 100 :=
  ⟨(613339223106798257988776994351142555241967419127466655764142564421248215399117793642073576850854910585977643378582737821550146172422270447701628734362427713808314388960217751120606925654917240337369871552616539843179815416913831070107370278027696434647658309512913784162514146044371985467508698557866393343078199683514232281677327732030033545430778694647984629127956848462066488851174693340639639709427238525767903718995118400453461079932020997498021071086330954193149581459110565966466991884475892761385986612124795034903985589665717141972919355282082543021878404732934679632067821940229077270943088836941075410359471079610221865219260658740223170617118834033938093916801716975953002274134482907679782181873646753357226426736797367589377731388215366523118707244937047334697137972462872900288240282044793951013371795323231897009892574618231193387396711021290984988208915048092134342226793031013430442480948022637131257933350618762706579385275159122985823657715986471138015301857638366548077828001014846176240070415671221886555220769092387790033757853023298093173453746406965376 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩
private def badActor (i : Fin 512) : Fin 512 :=
  ⟨(251042544797330036536738784696748812393433308107906339998130141672789204926299619646312560107670035159982265822451313844031965629338863132920541797682772747288748154070073472405677049330813720376367408707813045491693071814042642793681486788948121345173158128482630036475921892141920877636254872019236205299440308241058470259420257054689816032146059499785663400181306263239413177379636637672231872225774704300340647403481104888296968313311486750452092237775096 >>> (3 * i.val)) % 8, lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)⟩

private theorem smallRow_point : ∀ (j : Fin 8) (x : Fin 100),
    point (smallRow j) x = (small j : Equiv.Perm (Fin 100)) x := by
  apply allFin₂
  decide +kernel

private theorem smallRow_element (j : Fin 8) : element (smallRow j) = small j := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  rw [element_point]
  exact smallRow_point j x

private theorem rejection : ∀ i : Fin 512,
    i = smallRow (smallCode i) ∨
    point i (point i (badPoint i)) ≠ badPoint i ∨
    point i ((element (badActor i) : Equiv.Perm (Fin 100))
      (point i (((element (badActor i))⁻¹ : Equiv.Perm (Fin 100)) (badPoint i)))) ≠
    (element (badActor i) : Equiv.Perm (Fin 100))
      (point i (((element (badActor i))⁻¹ : Equiv.Perm (Fin 100)) (point i (badPoint i)))) := by
  apply allFin
  decide +kernel

/-- Squaring and commuting with conjugates exclude every row outside the elementary eight. -/
theorem small_of_normal_elementary_element (x : Carrier) (hx : x ∈ subgroup)
    (hsq : x ^ 2 = 1)
    (hc : ∀ g ∈ subgroup, x * (g * x * g⁻¹) = (g * x * g⁻¹) * x) :
    ∃ j : Fin 8, small j = x := by
  obtain ⟨i, rfl⟩ := element_surjective hx
  rcases rejection i with hi | hsqbad | hcbad
  · exact ⟨smallCode i, (smallRow_element _).symm.trans (congrArg element hi.symm)⟩
  · exfalso
    apply hsqbad
    have he := congrArg (fun g : Carrier => (g : Equiv.Perm (Fin 100)) (badPoint i)) hsq
    change (element i : Equiv.Perm (Fin 100))
      ((element i : Equiv.Perm (Fin 100)) (badPoint i)) = badPoint i at he
    simpa only [element_point] using he
  · exfalso
    apply hcbad
    have he := congrArg (fun g : Carrier => (g : Equiv.Perm (Fin 100)) (badPoint i))
      (hc (element (badActor i)) (element_mem _))
    change (element i : Equiv.Perm (Fin 100))
        ((element (badActor i) : Equiv.Perm (Fin 100))
          ((element i : Equiv.Perm (Fin 100))
            (((element (badActor i))⁻¹ : Equiv.Perm (Fin 100)) (badPoint i)))) =
      (element (badActor i) : Equiv.Perm (Fin 100))
        ((element i : Equiv.Perm (Fin 100))
          (((element (badActor i))⁻¹ : Equiv.Perm (Fin 100))
            ((element i : Equiv.Perm (Fin 100)) (badPoint i)))) at he
    simpa only [element_point] using he

end Sporadic.LeechRelated.HS.EvenLocalCandidates.SylowCatalogueData
