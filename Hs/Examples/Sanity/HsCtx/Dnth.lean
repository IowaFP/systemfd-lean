import Hs.HsTerm
import Hs.HsCtx


namespace HsCtx.dnth.Test

def BF : HsFrame HsTerm :=
   .datatypeDecl `★ [ `#0     -- Nothing :: ∀ a. Maybe a
                    , `#1        -- , (`∀{`★} `#0 → `#3 `•k `#1)  -- Just :: ∀ a. a -> Maybe a
                    ]


def MBCtx : HsFrame HsTerm :=
   .datatypeDecl (`★ `-k> `★) [ (`∀{`★} (`#1 `•k `#0))      -- Nothing :: ∀ a. Maybe a
                              , (`∀{`★} `#0 → `#3 `•k `#1)  -- Just :: ∀ a. a -> Maybe a
                              ]


def ctx : HsCtx HsTerm := [MBCtx, BF]
#eval ctx
#eval ctx.length

#eval (HsFrame.datatypeDecl `★ [ `#0 ]).width
#eval [HsFrame.datatypeDecl `★ [ `#0 ]] d@s 0
#eval [HsFrame.datatypeDecl `★ [ `#0 ]] d@s 1

#eval [HsFrame.datatypeDecl `★ [ `#0, `#1 ]] d@s 0
#eval [HsFrame.datatypeDecl `★ [ `#0, `#1 ]] d@s 1
#eval [HsFrame.datatypeDecl `★ [ `#0, `#1 ]] d@s 2


end HsCtx.dnth.Test
